import CoreGraphics
import CoreML
import Foundation
import NitroModules
import StableDiffusion
import UIKit

/**
 * Implements the `HybridImageGenSpec` protocol that `nitrogen` generates from
 * `../src/ImageGen.nitro.ts`. `nitrogen/generated/` is gitignored — run
 * `pnpm --filter @monodump/react-native-image-gen codegen` (required before
 * `pod install`; see README.md) to produce it, and re-run after editing the
 * spec.
 *
 * Wraps Apple's `StableDiffusionPipeline` (https://github.com/apple/ml-stable-diffusion),
 * the same library behind Apple's own `StableDiffusionSample` CLI tool. See
 * README.md for the required resources layout and the manual Xcode step
 * needed to link the `StableDiffusion` Swift package into this pod's target.
 */
class HybridImageGen: HybridImageGenSpec {
  private var pipeline: StableDiffusionPipeline?
  private var isCancelled = false

  func detectBackend() throws -> ImageGenBackend {
    return .iosCoreml
  }

  /**
   * `resourcesPath` must contain the compiled `.mlmodelc` bundles
   * (SafetyChecker, TextEncoder, Unet or UnetChunk1+UnetChunk2, VAEDecoder,
   * VAEEncoder) plus `vocab.json`/`merges.txt` — exactly the layout
   * ImageModelDownloadService downloads into
   * `<variant>/<split_einsum(_v2)>/compiled/`. `reduceMemory: true` streams
   * weights instead of holding every stage resident at once, which matters
   * on 6-8GB phones — see MemoryService/memoryBudget.ts for the RAM budget
   * this is gated behind before loadModel is ever called.
   */
  func loadModel(resourcesPath: String) throws -> Promise<Void> {
    return Promise.async {
      let config = MLModelConfiguration()
      config.computeUnits = .cpuAndNeuralEngine

      let resourcesURL = URL(fileURLWithPath: resourcesPath)
      let newPipeline = try StableDiffusionPipeline(
        resourcesAt: resourcesURL,
        // No ControlNet support — we don't download/expose any ControlNet models.
        controlNet: [],
        configuration: config,
        disableSafety: false,
        reduceMemory: true
      )
      try newPipeline.loadResources()

      self.pipeline = newPipeline
    }
  }

  /**
   * `previewEveryNSteps` controls how often `onProgress` fires — the ref
   * writeup on this pipeline is explicit that without a live preview users
   * think the app froze during the several-second denoising loop, even
   * though it's working. `seed: -1` means "pick a random seed".
   */
  func generate(
    prompt: String,
    negativePrompt: String,
    steps: Double,
    previewEveryNSteps: Double,
    seed: Double,
    onProgress: @escaping (ImageGenProgress) -> Void
  ) throws -> Promise<String> {
    guard let pipeline = self.pipeline else {
      throw RuntimeError.error(withMessage: "No image model loaded — call loadModel() first.")
    }
    isCancelled = false

    return Promise.async {
      var pipelineConfig = StableDiffusionPipeline.Configuration(prompt: prompt)
      pipelineConfig.negativePrompt = negativePrompt
      pipelineConfig.stepCount = max(1, Int(steps))
      pipelineConfig.guidanceScale = 7.5
      pipelineConfig.schedulerType = .dpmSolverMultistepScheduler
      pipelineConfig.seed = seed >= 0 ? UInt32(seed) : UInt32.random(in: 0..<UInt32.max)
      // Without this, PipelineProgress.currentImages decodes from the raw noisy latent at each
      // step instead of the denoised prediction — the doc comment on this flag literally says
      // it's "for better previews".
      pipelineConfig.useDenoisedIntermediates = true

      let previewInterval = max(1, Int(previewEveryNSteps))
      var lastImage: CGImage?

      let images = try pipeline.generateImages(configuration: pipelineConfig) { progress in
        if self.isCancelled { return false }

        // `currentImages` is a computed property that runs a full VAE decode on every access —
        // only touch it on the steps we're actually going to use, not every step.
        let isLastStep = progress.step == progress.stepCount - 1
        if progress.step % previewInterval == 0 || isLastStep {
          if let cgImage = progress.currentImages.first ?? nil {
            lastImage = cgImage
            if let previewPath = Self.writePNG(cgImage, prefix: "sd-preview") {
              onProgress(ImageGenProgress(
                step: Double(progress.step),
                totalSteps: Double(progress.stepCount),
                previewPath: previewPath
              ))
            }
          }
        }
        return true
      }

      guard let finalImage = (images.first ?? nil) ?? lastImage else {
        throw RuntimeError.error(withMessage: "Generation produced no image — it may have been blocked by the built-in safety checker, or cancelled.")
      }
      guard let resultPath = Self.writePNG(finalImage, prefix: "sd-result") else {
        throw RuntimeError.error(withMessage: "Generated an image but failed to write it to disk.")
      }
      return resultPath
    }
  }

  func cancelGeneration() throws -> Void {
    isCancelled = true
  }

  func unloadModel() throws -> Void {
    pipeline = nil
  }

  private static func writePNG(_ cgImage: CGImage, prefix: String) -> String? {
    let image = UIImage(cgImage: cgImage)
    guard let data = image.pngData() else { return nil }
    let path = NSTemporaryDirectory() + "\(prefix)-\(UUID().uuidString).png"
    do {
      try data.write(to: URL(fileURLWithPath: path))
      return path
    } catch {
      return nil
    }
  }
}
