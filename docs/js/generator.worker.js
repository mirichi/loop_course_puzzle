// Web Worker for asynchronous Loop Course puzzle generation
// Prevents UI thread blocking and browser freeze dialogs.

// Import dependencies using absolute or relative paths with cache-busters
importScripts("loopcourse.js?v=20260603_v15", "solver.js?v=20260603_v15", "generator.js?v=20260603_v15");

self.onmessage = function(e) {
  const { rows, cols, difficulty } = e.data;
  
  // Wait for WASM engine to load if it is still initializing, up to ~450ms (15 attempts)
  let wasmCheckAttempts = 0;
  const checkWasmAndGenerate = () => {
    if (typeof self.createLoopCourseModule === 'function' && !self.wasmReady && wasmCheckAttempts < 15) {
      wasmCheckAttempts++;
      setTimeout(checkWasmAndGenerate, 30);
      return;
    }
    
    try {
      const generator = new self.LoopCourseGenerator(rows, cols);
      const puzzle = generator.generate(difficulty);
      
      // Post puzzle results back to main thread
      self.postMessage({
        success: true,
        clues: puzzle.clues,
        solution: puzzle.solution,
        engineUsed: puzzle.engineUsed
      });
    } catch (err) {
      self.postMessage({
        success: false,
        error: err.message
      });
    }
  };
  
  checkWasmAndGenerate();
};
