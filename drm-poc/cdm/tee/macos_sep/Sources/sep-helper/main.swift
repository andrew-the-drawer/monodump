// sep-helper: a small CLI the Python side of Phase 6a shells out to, so that
// every private-key operation for our "device" happens inside the Secure
// Enclave rather than in a Python/JS process. See PLAN.md Part 4 (6a) and
// docs/02-tee.md for the design and its honest limits.
//
// Uses CryptoKit's `SecureEnclave` namespace rather than raw Security-
// framework `SecKeyCreateRandomKey(..., kSecAttrIsPermanent: true, ...)`.
// The latter persists the key as a real Keychain item, which on this
// machine failed with OSStatus -34018 (errSecMissingEntitlement) for an
// unsigned/ad-hoc-signed CLI binary, and, once an entitlements plist was
// added, hung indefinitely -- almost certainly an invisible Keychain
// consent UI with no window server session to show it in a non-interactive
// shell. CryptoKit's SecureEnclave keys sidestep this: the private key
// still never leaves the SEP, but *we* own persistence, via an opaque
// `dataRepresentation` blob we write to disk ourselves (Apple's documented
// mechanism for apps that don't want Keychain-managed storage). See
// docs/02-tee.md for the full account.
//
// Subcommands (all print one line of JSON to stdout on success; errors go
// to stderr with a non-zero exit code):
//   identity <label>                  generate-if-absent a persistent SE
//                                      P-256 signing key; print its public
//                                      JWK.
//   sign <label> <payload_b64url>      ECDSA-SHA256 sign with the identity
//                                      key, print raw r||s, base64url.
//   ecdh-session                       our protocol needs the client's
//                                      ephemeral public key *before* it
//                                      learns the server's (it's in the
//                                      signed /license request; the
//                                      server's key only comes back in the
//                                      response) -- a two-step exchange
//                                      that has to happen against the same
//                                      SE ephemeral key both times, without
//                                      ever writing that key to disk. So
//                                      this subcommand is a tiny stdin/
//                                      stdout session instead of a single
//                                      call: it generates a fresh SE
//                                      key-agreement key, prints
//                                      {"ephemeral_pubkey_jwk": ...} on line
//                                      1, then blocks for one line of stdin
//                                      shaped {"peer_x":.., "peer_y":..},
//                                      does the key exchange against that
//                                      same in-memory key, prints
//                                      {"shared_secret_b64": ...} on line 2,
//                                      and exits. The ephemeral private key
//                                      lives only inside this one process's
//                                      lifetime and is never persisted.
//   delete-identity <label>           remove a previously generated
//                                      identity key's blob (demo cleanup).

import CryptoKit
import Foundation
import Security

// MARK: - base64url

enum B64URL {
    static func encode(_ data: Data) -> String {
        var s = data.base64EncodedString()
        s = s.replacingOccurrences(of: "+", with: "-")
        s = s.replacingOccurrences(of: "/", with: "_")
        while s.hasSuffix("=") { s.removeLast() }
        return s
    }

    static func decode(_ s: String) -> Data? {
        var padded = s.replacingOccurrences(of: "-", with: "+")
        padded = padded.replacingOccurrences(of: "_", with: "/")
        while padded.count % 4 != 0 { padded += "=" }
        return Data(base64Encoded: padded)
    }
}

// MARK: - errors / output helpers

struct HelperError: Error, CustomStringConvertible {
    let message: String
    var description: String { message }
}

func fail(_ message: String) -> Never {
    FileHandle.standardError.write((message + "\n").data(using: .utf8)!)
    exit(1)
}

/// Writes one JSON line directly via the stdout file descriptor (not
/// Swift's `print`, which is fully buffered rather than line-buffered when
/// stdout is a pipe) — required for `ecdh-session`, where the caller must
/// see line 1 before it writes the stdin line this process blocks on next.
func printJSON(_ obj: [String: Any?]) {
    var clean: [String: Any] = [:]
    for (k, v) in obj { clean[k] = v ?? NSNull() }
    var data = try! JSONSerialization.data(withJSONObject: clean, options: [.sortedKeys])
    data.append(0x0A)
    FileHandle.standardOutput.write(data)
}

// MARK: - JWK helpers (P-256 raw representations, no 0x04 prefix, from CryptoKit)

func jwk(fromRawRepresentation rawIn: Data) throws -> [String: String] {
    let raw = Data(rawIn) // normalize to a zero-based Data, discarding any slice offset
    guard raw.count == 64 else {
        throw HelperError(message: "unexpected public key raw representation (\(raw.count) bytes)")
    }
    let x = raw.subdata(in: 0..<32)
    let y = raw.subdata(in: 32..<64)
    return ["kty": "EC", "crv": "P-256", "x": B64URL.encode(x), "y": B64URL.encode(y)]
}

func x963Representation(x xB64: String, y yB64: String) throws -> Data {
    guard let x = B64URL.decode(xB64), let y = B64URL.decode(yB64), x.count == 32, y.count == 32 else {
        throw HelperError(message: "malformed peer public key coordinates")
    }
    var rep = Data([0x04])
    rep.append(x)
    rep.append(y)
    return rep
}

// MARK: - on-disk identity storage
//
// Each label's SE signing key is represented on disk only by its opaque
// `dataRepresentation` blob -- see the file header. This is NOT the raw
// private key (see docs/02-tee.md's non-extractability proof, which shows
// exactly that: the blob can't be used as a P-256 scalar by anything other
// than the Secure Enclave that produced it). Gitignored; local demo state
// only, same convention as server/*.db and server/*.pem.

let identitiesDir: URL = {
    let dir = URL(fileURLWithPath: #filePath)
        .deletingLastPathComponent() // main.swift
        .deletingLastPathComponent() // sep-helper
        .deletingLastPathComponent() // Sources
        .appendingPathComponent(".identities")
    try? FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
    return dir
}()

func identityPath(_ label: String) -> URL {
    identitiesDir.appendingPathComponent("\(label).sepkey")
}

func accessControl() throws -> SecAccessControl {
    var cfError: Unmanaged<CFError>?
    guard let access = SecAccessControlCreateWithFlags(
        nil, kSecAttrAccessibleWhenUnlockedThisDeviceOnly, [.privateKeyUsage], &cfError
    ) else {
        let msg = cfError.map { CFErrorCopyDescription($0.takeRetainedValue()) as String } ?? "unknown error"
        throw HelperError(message: "SecAccessControlCreateWithFlags failed: \(msg)")
    }
    return access
}

func loadOrCreateIdentityKey(_ label: String) throws -> SecureEnclave.P256.Signing.PrivateKey {
    let path = identityPath(label)
    if let existing = try? Data(contentsOf: path) {
        return try SecureEnclave.P256.Signing.PrivateKey(dataRepresentation: existing)
    }
    let key = try SecureEnclave.P256.Signing.PrivateKey(accessControl: try accessControl())
    try key.dataRepresentation.write(to: path, options: [.atomic])
    return key
}

// MARK: - subcommands

// No attestation subcommand: we looked for a supported way to get a real
// Apple-rooted attestation of this key (SecKeyCreateAttestation exists in
// the Security.framework binary but has no public header on macOS across
// SDKs 11-26; DCAppAttestService.supported is documented to be false on
// every Mac target including Apple silicon) and came up empty. See
// docs/02-tee.md for the investigation. What device.py builds instead is a
// proof-of-possession claim -- a fresh signature over a timestamped payload,
// made via the `sign` subcommand below -- which is real (only this SE key
// could have produced it) but is not equivalent to third-party attestation
// of the key's hardware origin.
func cmdIdentity(_ args: [String]) throws {
    guard args.count == 1 else { throw HelperError(message: "usage: identity <label>") }
    guard SecureEnclave.isAvailable else {
        throw HelperError(message: "Secure Enclave not available on this machine")
    }
    let key = try loadOrCreateIdentityKey(args[0])
    let jwkOut = try jwk(fromRawRepresentation: key.publicKey.rawRepresentation)
    printJSON(["pubkey_jwk": jwkOut])
}

func cmdSign(_ args: [String]) throws {
    guard args.count == 2 else { throw HelperError(message: "usage: sign <label> <payload_b64url>") }
    let path = identityPath(args[0])
    guard let stored = try? Data(contentsOf: path) else {
        throw HelperError(message: "no identity key for label '\(args[0])' — run `identity` first")
    }
    let key = try SecureEnclave.P256.Signing.PrivateKey(dataRepresentation: stored)
    guard let payload = B64URL.decode(args[1]) else {
        throw HelperError(message: "malformed payload")
    }
    let signature = try key.signature(for: payload)
    printJSON(["signature_b64": B64URL.encode(signature.rawRepresentation)])
}

func cmdEcdhSession() throws {
    guard SecureEnclave.isAvailable else {
        throw HelperError(message: "Secure Enclave not available on this machine")
    }

    // Never written to disk: this key exists only for the lifetime of this
    // process and this one exchange, exactly like a WebCrypto ephemeral
    // ECDH key that's never marked extractable. Once this process exits,
    // there is no way to get it back — not even for us.
    let ephemeralKey = try SecureEnclave.P256.KeyAgreement.PrivateKey(accessControl: try accessControl())
    let ephemeralJWK = try jwk(fromRawRepresentation: ephemeralKey.publicKey.rawRepresentation)
    printJSON(["ephemeral_pubkey_jwk": ephemeralJWK])

    guard let line = readLine(strippingNewline: true), let lineData = line.data(using: .utf8) else {
        throw HelperError(message: "expected one line of JSON {\"peer_x\":..,\"peer_y\":..} on stdin")
    }
    guard let request = try JSONSerialization.jsonObject(with: lineData) as? [String: Any],
          let peerX = request["peer_x"] as? String, let peerY = request["peer_y"] as? String else {
        throw HelperError(message: "malformed stdin request, expected {\"peer_x\":..,\"peer_y\":..}")
    }

    let peerRep = try x963Representation(x: peerX, y: peerY)
    let peerPublicKey = try P256.KeyAgreement.PublicKey(x963Representation: peerRep)
    let sharedSecret = try ephemeralKey.sharedSecretFromKeyAgreement(with: peerPublicKey)
    let sharedSecretBytes = sharedSecret.withUnsafeBytes { Data($0) }
    printJSON(["shared_secret_b64": B64URL.encode(sharedSecretBytes)])
}

func cmdDeleteIdentity(_ args: [String]) throws {
    guard args.count == 1 else { throw HelperError(message: "usage: delete-identity <label>") }
    let path = identityPath(args[0])
    let existed = FileManager.default.fileExists(atPath: path.path)
    try? FileManager.default.removeItem(at: path)
    printJSON(["deleted": existed])
}

// MARK: - entry point

let arguments = CommandLine.arguments
guard arguments.count >= 2 else {
    fail("usage: sep-helper <identity|sign|ecdh-session|delete-identity> [args...]")
}

do {
    switch arguments[1] {
    case "identity": try cmdIdentity(Array(arguments.dropFirst(2)))
    case "sign": try cmdSign(Array(arguments.dropFirst(2)))
    case "ecdh-session": try cmdEcdhSession()
    case "delete-identity": try cmdDeleteIdentity(Array(arguments.dropFirst(2)))
    default: fail("unknown subcommand '\(arguments[1])'")
    }
} catch {
    fail("\(error)")
}
