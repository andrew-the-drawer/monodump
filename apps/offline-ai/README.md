Everything I learned building on-device AI into a React Native app -- LLMs, Stable Diffusion, Whisper, and Vision

I spent some time building a React Native app that runs LLMs, image generation, voice transcription, and vision AI entirely on-device. No cloud. No API keys. Works in airplane mode.

Here's what I wish someone had told me before I started. If you're thinking about adding on-device AI to an RN app, this should save you some pain.

Text generation (LLMs)

Use llama.rn. It's the only serious option for running GGUF models in React Native. It wraps llama.cpp and gives you native bindings for both Android (JNI) and iOS (Metal). Streaming tokens via callbacks works well.

The trap: you'll think "just load the model and call generate." The real work is everything around that. Memory management is the whole game on mobile. A 7B Q4 model needs ~5.5GB of RAM at runtime (file size x 1.5 for KV cache and activations). Most phones have 6-8GB total and the OS wants half of it. You need to calculate whether a model will fit BEFORE you try to load it, or the OS silently kills your app and users think it crashed.

I use 60% of device RAM as a hard budget. Warn at 50%, block at 60%. Human-readable error messages. This one thing prevents more 1-star reviews than any feature you'll build.

GPU acceleration: OpenCL on Android (Adreno GPUs), Metal on iOS. Works, but be careful -- flash attention crashes with GPU layers > 0 on Android. Enforce this in code so users never hit it. KV cache quantization (f16/q8_0/q4_0) is a bigger win than GPU for most devices. Going from f16 to q4_0 roughly tripled inference speed in my testing.

Image generation (Stable Diffusion)

This is where it gets platform-specific. No single library covers both.

Android: look at MNN (Alibaba's framework, CPU, works on all ARM64 devices) and QNN (Qualcomm AI Engine, NPU-accelerated, Snapdragon 8 Gen 1+ only). QNN is 3x faster but only works on recent Qualcomm chips. You want runtime detection with automatic fallback.

iOS: Apple's ml-stable-diffusion pipeline with Core ML. Neural Engine acceleration. Their palettized models (~1GB, 6-bit) are great for memory-constrained devices. Full precision (~4GB, fp16) is faster on ANE but needs the headroom.

Real-world numbers: 5-10 seconds on Snapdragon NPU, 15 seconds CPU on flagship, 8-15 seconds iOS ANE. 512x512 at 20 steps.

The key UX decision: show real-time preview every N denoising steps. Without it, users think the app froze. With it, they watch the image form and it feels fast even when it's not.

Voice (Whisper)

whisper.rn wraps whisper.cpp. Straightforward to integrate. Offer multiple model sizes (Tiny/Base/Small) and let users pick their speed vs accuracy tradeoff. Real-time partial transcription (words appearing as they speak) is what makes it feel native vs "processing your audio."

One thing: buffer audio in native code and clear it after transcription. Don't write audio files to disk if privacy matters to your users.

Vision (multimodal models)

Vision models need two files -- the main GGUF and an mmproj (multimodal projector) companion. This is terrible UX if you expose it to users. Handle it transparently: auto-detect vision models, auto-download the mmproj, track them as a single unit, search the model directory at runtime if the link breaks.

Download both files in parallel, not sequentially. On a 2B vision model this cuts download time nearly in half.

SmolVLM at 500M is the sweet spot for mobile -- ~7 seconds on flagship, surprisingly capable for document reading and scene description.

Tool calling (on-device agent loops)

This one's less obvious but powerful. Models that support function calling can use tools -- web search, calculator, date/time, device info -- through an automatic loop: LLM generates, you parse for tool calls, execute them, inject results back into context, LLM continues. Cap it (I use max 3 iterations, 5 total calls) or the model will loop forever.

Two parsing paths are critical. Larger models output structured JSON tool calls natively through llama.rn. Smaller models output XML like <tool_call>. If you only handle JSON, you cut out half the models that technically support tools but don't format them cleanly. Support both.

Capability gating matters. Detect tool support at model load time by inspecting the jinja chat template. If the model doesn't support tools, don't inject tool definitions into the system prompt -- smaller models will see them and hallucinate tool calls they can't execute. Disable the tools UI entirely for those models.

The calculator uses a recursive descent parser. Never eval(). Ever.

Intent classification (text vs image generation)

If your app does both text and image gen, you need to decide what the user wants. "Draw a cute dog" should trigger Stable Diffusion. "Tell me about dogs" should trigger the LLM. Sounds simple until you hit edge cases.

Two approaches: pattern matching (fast, keyword-based -- "draw," "generate," "create image") or LLM-based classification (slower, uses your loaded text model to classify intent). Pattern matching is instant but misses nuance. LLM classification is more accurate but adds latency before generation even starts.

I ship both and let users choose. Default to pattern matching. Offer a manual override toggle that forces image gen mode for the current message. The override is important -- when auto-detection gets it wrong, users need a way to correct it without rewording their message.

Prompt enhancement (the LLM-to-image-gen handoff)

Simple user prompts make bad Stable Diffusion inputs. "A dog" produces generic output. But if you run that prompt through your loaded text model first with an enhancement system prompt, you get a ~75-word detailed description with artistic style, lighting, composition, and quality modifiers. The output quality difference is dramatic.

The gotcha that cost me real debugging time: after enhancement finishes, you need to call stopGeneration() to reset the LLM state. But do NOT clear the KV cache. If you clear KV cache after every prompt enhancement, your next vision inference takes 30-60 seconds longer. The cache from the text model helps subsequent multimodal loads. Took me a while to figure out why vision got randomly slow.

Model discovery and HuggingFace integration

You need to help users find models that actually work on their device. This means HuggingFace API integration with filtering by device RAM, quantization level, model type (text/vision/code), organization, and size category.

The important part: calculate whether a model will fit on the user's specific device BEFORE they download 4GB over cellular. Show RAM requirements next to every model. Filter out models that won't fit. For vision models, show the combined size (GGUF + mmproj) because users don't know about the companion file.

Curate a recommended list. Don't just dump the entire HuggingFace catalog. Pick 5-6 models per capability that you've tested on real mid-range hardware. Qwen 3, Llama 3.2, Gemma 3, SmolLM3, Phi-4 cover most use cases. For vision, SmolVLM is the obvious starting point.

Support local import too. Let users pick a .gguf file from device storage via the native file picker. Parse the model name and quantization from the filename. Handle Android content:// URIs (you'll need to copy to app storage). Some users have models already and don't want to re-download.

The architectural decisions that actually matter

Singleton services for anything touching native inference. If two screens try to load different models at the same time, you get a SIGSEGV. Not an exception. A dead process. Guard every load with a promise check.

Background-safe generation. Your generation service needs to live outside React component lifecycle. Use a subscriber pattern -- screens subscribe on mount, get current state immediately, unsubscribe on unmount. Generation continues regardless of what screen the user is on. Without this, navigating away kills your inference mid-stream.

Service-store separation. Services write to Zustand stores, UI reads from stores. Services own the long-running state. Components are just views. This sounds obvious but it's tempting to put generation state in component state and you'll regret it the first time a user switches tabs during a 15-second image gen.

Memory checks before every model load. Not optional. Calculate required RAM (file size x 1.5 for text, x 1.8 for image gen), compare against device budget, block if it won't fit. The alternative is random OOM crashes that you can't reproduce in development because your test device has 12GB.

Native download manager on Android. RN's JS networking dies when the app backgrounds. Android's DownloadManager survives. Bridge to it. Watch for a race condition where the completion broadcast arrives before RN registers its listener -- track event delivery with a boolean flag.

What I'd do differently

Start with text generation only. Get the memory management, model loading, and background-safe generation pattern right. Then add image gen, then vision, then voice. Each one reuses the same architectural patterns (singleton service, subscriber pattern, memory budget) but has its own platform-specific quirks. The foundation matters more than the features.

Don't try to support every model. Pick 3-4 recommended models per capability, test them thoroughly on real mid-range devices (not just your flagship), and document the performance. Users with 6GB phones running a 7B model and getting 3 tok/s will blame your app, not their hardware.

Happy to answer questions about any of this. Especially the memory management, tool calling implementation, or the platform-specific image gen decisions.