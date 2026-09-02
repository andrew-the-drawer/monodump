require "json"

package = JSON.parse(File.read(File.join(__dir__, "package.json")))

Pod::Spec.new do |s|
  s.name         = "ReactNativeImageGen"
  s.version      = package["version"]
  s.summary      = package["description"]
  s.homepage     = "https://github.com/lantrungseo/monodump"
  s.license      = "MIT"
  s.authors      = "lantrungseo"
  # Apple's ml-stable-diffusion StableDiffusionPipeline requires iOS 16.2+.
  s.platforms    = { ios: "16.2" }
  s.source       = { git: "" }

  s.source_files = [
    # Hand-written implementation.
    "ios/**/*.{swift,h,m,mm,cpp}",
  ]

  s.pod_target_xcconfig = {
    "SWIFT_COMPILATION_MODE" => "wholemodule",
  }

  # Adds the nitrogen-generated C++/Swift bridge files to s.source_files, and — critically —
  # merges in CLANG_CXX_LANGUAGE_STANDARD=c++20 and SWIFT_OBJC_INTEROP_MODE=objcxx into
  # pod_target_xcconfig. Without that second one specifically, Swift's ClangImporter parses
  # NitroModules' C++ headers (e.g. cpp/core/Null.hpp) as plain C, which is what produces the
  # confusing "'functional' file not found" error — the header search paths clang sets up for a
  # plain-C parse don't include libc++. See nitrogen/generated/ios/ReactNativeImageGen+autolinking.rb.
  load 'nitrogen/generated/ios/ReactNativeImageGen+autolinking.rb'
  add_nitrogen_files(s)

  # Apple's ml-stable-diffusion pipeline (the `StableDiffusion` product of
  # https://github.com/apple/ml-stable-diffusion) is SPM-only — there's no published podspec for
  # it, so a plain `s.dependency` can't resolve it. `spm_dependency` is provided by the
  # `cocoapods-spm` plugin (Gemfile + `plugin 'cocoapods-spm'` — see
  # apps/offline-ai/plugins/withStableDiffusionSpmPackage.js, which re-declares the matching
  # `spm_pkg "stable-diffusion", :git => ...` in ios/Podfile on every `expo prebuild`, since
  # ios/ itself is gitignored/regenerated). See README.md.
  #
  # "stable-diffusion" (not the repo name "ml-stable-diffusion", and not an arbitrary label) is
  # the exact `name:` Apple's own Package.swift declares — cocoapods-spm resolves this by matching
  # that real declared name, not by whatever we'd prefer to call it.
  s.spm_dependency "stable-diffusion/StableDiffusion"

  install_modules_dependencies(s)
end
