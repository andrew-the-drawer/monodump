// Phase 2: wire shaka-player against org.w3.clearkey, license server at
// /clearkey-license. Phase 3+ adds a second path that runs our own
// provisioning + license protocol in-browser via WebCrypto, then feeds the
// resulting raw keys to the same ClearKey CDM (see loadWithProtocol below).

const MANIFEST_URL = '/content/dash.mpd';
const CLEARKEY_LICENSE_URL = '/clearkey-license';

const logEl = document.getElementById('log');
const tierEl = document.getElementById('tier');
let player = null;

function log(...args) {
  const line = args.map(a => (typeof a === 'string' ? a : JSON.stringify(a))).join(' ');
  logEl.textContent += line + '\n';
  logEl.scrollTop = logEl.scrollHeight;
  console.log(...args);
}

function trackLabel(track) {
  if (track.type === 'variant') {
    return `${track.height}p @ ${Math.round(track.videoBandwidth / 1000)}kbps`;
  }
  return track.type;
}

async function initPlayer() {
  shaka.polyfill.installAll();
  if (!shaka.Player.isBrowserSupported()) {
    log('ERROR: browser not supported by shaka-player');
    return null;
  }
  const video = document.getElementById('video');
  const p = new shaka.Player();
  await p.attach(video);
  p.addEventListener('error', (event) => log('PLAYER ERROR', event.detail.code, event.detail.message));
  p.addEventListener('adaptation', () => {
    const active = p.getVariantTracks().find(t => t.active);
    if (active) tierEl.textContent = `playing: ${trackLabel(active)}`;
  });
  return p;
}

async function loadWithClearKey() {
  player.configure({
    drm: {
      servers: { 'org.w3.clearkey': CLEARKEY_LICENSE_URL },
    },
  });
  log('loading manifest via Phase 2 ClearKey path ->', CLEARKEY_LICENSE_URL);
  await player.load(MANIFEST_URL);
  log('loaded. variant tracks:', player.getVariantTracks().map(trackLabel));
}

// --- Phase 3+: our own provisioning + license protocol, run entirely in the
// browser via WebCrypto. See docs/01-protocol.md for the wire spec this
// mirrors byte-for-byte with server/crypto.py and tools/protocol_client.py.

const CONTENT_ID = 'demo';
const HKDF_INFO = new TextEncoder().encode('drm-poc-license-v1');
// Phase 3-5 stand-in for real TEE attestation -- see docs/01-protocol.md.
// Hardcoded here because there is no real hardware root of trust until
// Phase 6; anyone reading this file can see it, which is the point.
const SIMULATED_ATTESTATION_SECRET = 'dev-only-simulated-tee-attestation-v1';

function b64urlEncode(bytes) {
  let bin = '';
  for (const b of bytes) bin += String.fromCharCode(b);
  return btoa(bin).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}

function b64urlDecode(str) {
  const padded = str.replace(/-/g, '+').replace(/_/g, '/') + '==='.slice((str.length + 3) % 4);
  const bin = atob(padded);
  const bytes = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
  return bytes;
}

async function discoverKids(manifestUrl) {
  const text = await (await fetch(manifestUrl)).text();
  const kids = new Set();
  for (const m of text.matchAll(/cenc:default_KID="([0-9a-fA-F-]+)"/g)) {
    kids.add(m[1].replace(/-/g, '').toLowerCase());
  }
  return [...kids];
}

async function provisionDevice(securityLevel) {
  const identityKeyPair = await crypto.subtle.generateKey(
    { name: 'ECDSA', namedCurve: 'P-256' }, false, ['sign', 'verify']
  );
  const identityPubkeyJwk = await crypto.subtle.exportKey('jwk', identityKeyPair.publicKey);
  const attestation = securityLevel === 'TEE' ? SIMULATED_ATTESTATION_SECRET : undefined;

  const resp = await fetch('/provision', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      identity_pubkey_jwk: identityPubkeyJwk,
      requested_security_level: securityLevel,
      attestation,
    }),
  });
  if (!resp.ok) throw new Error(`provision failed: ${resp.status} ${await resp.text()}`);
  const data = await resp.json();
  log('provisioned device', data.device_id, 'security_level =', data.security_level);
  return {
    identityPrivateKey: identityKeyPair.privateKey,
    deviceId: data.device_id,
    masterToken: data.master_token,
    securityLevel: data.security_level,
  };
}

async function requestLicense(device, contentId, kids, sessionId) {
  const nonceBytes = crypto.getRandomValues(new Uint8Array(16));
  const nonceB64 = b64urlEncode(nonceBytes);
  const ephemeralKeyPair = await crypto.subtle.generateKey(
    { name: 'ECDH', namedCurve: 'P-256' }, false, ['deriveBits']
  );
  const ephemeralPubJwk = await crypto.subtle.exportKey('jwk', ephemeralKeyPair.publicKey);

  const sortedKids = [...kids].map(k => k.toLowerCase()).sort().join(',');
  const payloadStr = `${contentId}|${sortedKids}|${nonceB64}|${ephemeralPubJwk.x}.${ephemeralPubJwk.y}`;
  const signatureBytes = new Uint8Array(await crypto.subtle.sign(
    { name: 'ECDSA', hash: 'SHA-256' }, device.identityPrivateKey, new TextEncoder().encode(payloadStr)
  ));

  const resp = await fetch('/license', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      master_token: device.masterToken,
      content_id: contentId,
      kids,
      nonce: nonceB64,
      ephemeral_pubkey_jwk: ephemeralPubJwk,
      signature: b64urlEncode(signatureBytes),
      session_id: sessionId || null,
    }),
  });
  if (!resp.ok) {
    const body = await resp.json().catch(() => ({}));
    return { ok: false, status: resp.status, reason: body.detail };
  }
  const data = await resp.json();

  const serverPubKey = await crypto.subtle.importKey(
    'jwk', data.server_ephemeral_pubkey_jwk, { name: 'ECDH', namedCurve: 'P-256' }, false, []
  );
  const sharedBits = await crypto.subtle.deriveBits(
    { name: 'ECDH', public: serverPubKey }, ephemeralKeyPair.privateKey, 256
  );
  const hkdfKey = await crypto.subtle.importKey('raw', sharedBits, 'HKDF', false, ['deriveBits']);
  const okm = new Uint8Array(await crypto.subtle.deriveBits(
    { name: 'HKDF', hash: 'SHA-256', salt: nonceBytes, info: HKDF_INFO }, hkdfKey, 512
  ));
  const encKeyBytes = okm.slice(0, 32);
  const macKeyBytes = okm.slice(32, 64);

  const ivBytes = b64urlDecode(data.iv);
  const ctBytes = b64urlDecode(data.ciphertext);
  const macBytes = b64urlDecode(data.mac);
  const ephJwk = data.server_ephemeral_pubkey_jwk;
  const macInput = new TextEncoder().encode(`${ephJwk.x}.${ephJwk.y}`);
  const macInputFull = new Uint8Array(macInput.length + ivBytes.length + ctBytes.length);
  macInputFull.set(macInput, 0);
  macInputFull.set(ivBytes, macInput.length);
  macInputFull.set(ctBytes, macInput.length + ivBytes.length);

  const macKey = await crypto.subtle.importKey(
    'raw', macKeyBytes, { name: 'HMAC', hash: 'SHA-256' }, false, ['verify']
  );
  const macOk = await crypto.subtle.verify('HMAC', macKey, macBytes, macInputFull);
  if (!macOk) throw new Error('license response MAC verification failed — discarding');

  const encKey = await crypto.subtle.importKey('raw', encKeyBytes, 'AES-GCM', false, ['decrypt']);
  const plaintext = new Uint8Array(await crypto.subtle.decrypt(
    { name: 'AES-GCM', iv: ivBytes }, encKey, ctBytes
  ));
  const payload = JSON.parse(new TextDecoder().decode(plaintext));
  return { ok: true, ...payload };
}

async function loadWithProtocol() {
  const securityLevel = document.getElementById('securityLevel').value;
  const kids = await discoverKids(MANIFEST_URL);
  log('discovered KIDs from manifest:', kids);

  const device = await provisionDevice(securityLevel);
  const result = await requestLicense(device, CONTENT_ID, kids, null);
  if (!result.ok) {
    log('LICENSE DENIED:', result.status, result.reason);
    throw new Error(`license denied: ${result.reason}`);
  }
  log('license granted. session', result.session_id, 'policy', result.policy);
  log('keys received for KIDs:', Object.keys(result.keys),
      `(${Object.keys(result.keys).length} of ${kids.length} requested — the gap is Phase 5 tier gating)`);

  player.configure({ drm: { clearKeys: result.keys } });
  await player.load(MANIFEST_URL);
  log('loaded via our protocol. variant tracks:', player.getVariantTracks().map(trackLabel));

  // Phase 4: periodic renewal, torn down on any policy rejection (revocation,
  // rental window, concurrency). ClearKey has no native per-key expiry, so
  // policy enforcement after the initial grant is modeled as "renewal gets
  // rejected -> we stop playback," not "the CDM's existing keys stop
  // working." See docs/01-protocol.md for why that's an honest scope cut.
  const ttlMs = (result.policy.expires_at - Date.now() / 1000) * 1000;
  const renewalDelay = Math.max(ttlMs * 0.7, 1000);
  const sessionId = result.session_id;
  const scheduleRenewal = () => setTimeout(async () => {
    const renewal = await requestLicense(device, CONTENT_ID, kids, sessionId);
    if (!renewal.ok) {
      log('RENEWAL REJECTED:', renewal.status, renewal.reason, '-> stopping playback');
      document.getElementById('video').pause();
      tierEl.textContent = `stopped: ${renewal.reason}`;
      return;
    }
    log('renewed. new policy', renewal.policy);
    scheduleRenewal();
  }, renewalDelay);
  scheduleRenewal();
}

async function loadSelected() {
  logEl.textContent = '';
  if (!player) player = await initPlayer();
  if (!player) return;
  const mode = document.getElementById('mode').value;
  try {
    if (mode === 'clearkey') {
      await loadWithClearKey();
    } else {
      await loadWithProtocol();
    }
  } catch (e) {
    log('LOAD FAILED', e.code || '', e.message || e);
  }
}

// --- Real hardware security-level probe ---------------------------------
// Unrelated to our simulated SW/TEE protocol above. EME gives JS no direct
// "what's my security level" getter (that would be a fingerprinting/spoofing
// surface) — instead you PROBE by requesting: ask for a specific
// `robustness` string, and the promise only resolves if the platform's
// actual CDM meets that bar. Real players (Netflix included) walk these from
// strongest to weakest and use whichever first resolves. This queries
// whatever CDM Chrome actually has on this machine — on desktop Chrome/macOS
// that's always software-only Widevine (no L1), which is itself the point:
// desktop Widevine doesn't route through the Secure Enclave at all, so even
// a machine with real hardware-backed keys (ours, via SEP) reports as
// software-secure to EME. See docs/02-tee.md (Phase 6) for why.
const VIDEO_CODEC = 'video/mp4; codecs="avc1.640028"'; // matches our fhd/uhd tiers
const AUDIO_CODEC = 'audio/mp4; codecs="mp4a.40.2"';

const ROBUSTNESS_PROBES = {
  'com.widevine.alpha': [
    'HW_SECURE_ALL',
    'HW_SECURE_DECODE',
    'HW_SECURE_CRYPTO',
    'SW_SECURE_DECODE',
    'SW_SECURE_CRYPTO',
    '', // no robustness requested at all -- whatever the CDM defaults to
  ],
  'com.microsoft.playready.recommendation': ['3000', '2000', '150', ''],
};

function withTimeout(promise, ms, label) {
  return Promise.race([
    promise,
    new Promise((_, reject) => setTimeout(() => reject(new Error(`timed out after ${ms}ms (${label})`)), ms)),
  ]);
}

async function probeKeySystem(keySystem, robustnessLevels) {
  const results = [];
  for (const robustness of robustnessLevels) {
    const config = [{
      initDataTypes: ['cenc'],
      videoCapabilities: [{ contentType: VIDEO_CODEC, robustness }],
      audioCapabilities: [{ contentType: AUDIO_CODEC, robustness: '' }],
    }];
    try {
      // A CDM component (esp. Widevine) not yet downloaded/warmed by the
      // browser can make this hang far longer than a real rejection would
      // take -- cap it so the probe always finishes instead of hanging.
      const access = await withTimeout(
        navigator.requestMediaKeySystemAccess(keySystem, config), 4000, keySystem
      );
      results.push({ robustness: robustness || '(default)', supported: true });
      // First (strongest) success tells us the ceiling; stop here.
      try {
        const mediaKeys = await access.createMediaKeys();
        if (mediaKeys.getStatusForPolicy) {
          const hdcp22 = await mediaKeys.getStatusForPolicy({ minHdcpVersion: '2.2' });
          results[results.length - 1].hdcp22 = hdcp22; // 'usable' | 'output-restricted' | ...
        }
      } catch (e) {
        // getStatusForPolicy is not implemented everywhere; not fatal.
      }
      break;
    } catch (e) {
      const timedOut = /^timed out/.test(e.message || '');
      results.push({ robustness: robustness || '(default)', supported: false, timedOut });
      if (timedOut) break; // don't keep waiting 4s per level if the CDM component isn't warm
    }
  }
  return results;
}

async function probeHardwareSecurityLevel() {
  log('--- probing real platform CDM(s) via EME robustness negotiation ---');
  for (const [keySystem, levels] of Object.entries(ROBUSTNESS_PROBES)) {
    try {
      const results = await probeKeySystem(keySystem, levels);
      const highest = results.find(r => r.supported);
      const timedOut = results.some(r => r.timedOut);
      if (highest) {
        log(keySystem, '-> highest supported robustness:', highest.robustness,
            highest.hdcp22 ? `(HDCP 2.2 policy: ${highest.hdcp22})` : '');
      } else if (timedOut) {
        log(keySystem, "-> timed out (CDM component likely not downloaded/warm yet in this",
            'browser profile -- try again in a few seconds, or after using any DRM site once)');
      } else {
        log(keySystem, '-> not available in this browser at all');
      }
      log('  full probe:', results);
    } catch (e) {
      log(keySystem, '-> probe failed:', e.message || e);
    }
  }
  log('note: FairPlay (Safari-only) uses a different, older API shape');
  log('(WebKitMediaKeys) and cannot be probed this way from Chrome.');
}

document.getElementById('probe').addEventListener('click', probeHardwareSecurityLevel);

document.getElementById('load').addEventListener('click', loadSelected);

// ?autoload=clearkey|protocol|probe&level=SW|TEE drives the page without a
// click, for headless verification (see README "verifying without a human").
const params = new URLSearchParams(location.search);
const autoload = params.get('autoload');
if (autoload === 'probe') {
  window.addEventListener('load', probeHardwareSecurityLevel);
} else if (autoload) {
  document.getElementById('mode').value = autoload;
  const level = params.get('level');
  if (level) document.getElementById('securityLevel').value = level;
  window.addEventListener('load', loadSelected);
}
