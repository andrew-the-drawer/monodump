// swift-tools-version:5.9
import PackageDescription

let package = Package(
    name: "sep-helper",
    platforms: [.macOS(.v13)],
    targets: [
        .executableTarget(name: "sep-helper", path: "Sources/sep-helper")
    ]
)
