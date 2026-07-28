class LoopCourseGame {
  constructor() {
    this.rows = 7;
    this.cols = 7;
    this.difficulty = 'medium';

    this.clues = [];
    this.solution = []; // original generated loop
    this.edgeStates = []; // 0 = empty, 1 = line, -1 = cross

    // History stacks for Undo / Redo
    this.undoStack = [];
    this.redoStack = [];
    this.currentDragGroup = []; // Accumulates changes during a single drag operation

    // UI Interaction states
    this.isDragging = false;
    this.dragState = 0; // State being painted: -1, 0, or 1

    // Timer
    this.timerInterval = null;
    this.secondsElapsed = 0;
    this.isPaused = false;
    this.gameCompleted = false;
    this.hintFailedOnce = false;
    this.isTouchMode = false;
    this.autoColorEnabled = false;

    // Pan & Zoom state
    this.zoomScale = 1.0;
    this.panX = 0;
    this.panY = 0;
    this.minZoom = 0.05;
    this.maxZoom = 4.0;
    this.hasManuallyAdjusted = false;
    this.lastContainerW = 0;
    this.lastContainerH = 0;

    // Layout parameters
    this.spacing = 54; // Distance between dots in px
    this.padding = 60; // Border padding in px

    this.initDOM();
    if (!this.checkCustomPuzzleLoad()) {
      this.startNewGame();
    }
  }

  initDOM() {
    this.svg = document.getElementById('game-svg');
    this.svgContainer = document.querySelector('.svg-container');
    this.timerEl = document.getElementById('timer-value');
    this.statusTextEl = document.getElementById('status-text');
    this.undoBtn = document.getElementById('btn-undo');
    this.redoBtn = document.getElementById('btn-redo');

    this.coloringTimeout = null;

    // Setup event listeners for settings
    document.getElementById('btn-new-game').addEventListener('click', () => this.startNewGame());
    const loadFileBtn = document.getElementById('btn-load-file');
    const fileInput = document.getElementById('file-input');
    if (loadFileBtn && fileInput) {
      loadFileBtn.addEventListener('click', () => fileInput.click());
      fileInput.addEventListener('change', (e) => this.handleFileUpload(e));
    }

    // Setup Lab return button listeners to guarantee exact puzzle string transfer
    document.querySelectorAll('a[href="lab.html"], #btn-modal-lab').forEach(btn => {
      btn.addEventListener('click', (e) => {
        e.preventDefault();
        this.goToLab();
      });
    });

    // Disable browser context menu on the entire board to allow smooth right-click tool usage
    this.svg.addEventListener('contextmenu', (e) => e.preventDefault());

    // Global board mousedown: initiate dragging even from empty spaces
    this.svg.addEventListener('mousedown', (e) => {
      if (this.gameCompleted || this.isPaused || this.isTouchMode) return;
      // Allow left-click (0) for drawing lines and right-click (2) for crosses
      if (e.button !== 0 && e.button !== 2) return;
      // If we clicked directly on an edge hitbox, let the hitbox handle it (to toggle correctly)
      if (e.target.classList.contains('edge-hitbox')) return;

      this.isDragging = true;
      this.lastMouseX = e.clientX;
      this.lastMouseY = e.clientY;
      this.mouseHistory = [{ x: e.clientX, y: e.clientY, time: Date.now() }];

      const startSVG = this.getSVGCoords(e.clientX, e.clientY);
      this.lastSVGX = startSVG.x;
      this.lastSVGY = startSVG.y;

      const isRightClick = e.button === 2;
      if (isRightClick) {
        this.dragState = -1; // Cross
      } else {
        this.dragState = 1; // Line
      }
    });



    this.undoBtn.addEventListener('click', () => this.undo());
    this.redoBtn.addEventListener('click', () => this.redo());
    const btnCheck = document.getElementById('btn-check');
    if (btnCheck) {
      btnCheck.addEventListener('click', () => this.checkMistakes());
    }
    const autoColorBtn = document.getElementById('btn-autocolor');
    if (autoColorBtn) {
      autoColorBtn.addEventListener('click', () => {
        this.autoColorEnabled = !this.autoColorEnabled;
        if (this.autoColorEnabled) {
          autoColorBtn.classList.add('active');
        } else {
          autoColorBtn.classList.remove('active');
        }
        this.scheduleAutoColoring();
      });
    }
    document.getElementById('btn-hint').addEventListener('click', () => this.giveHint());
    document.getElementById('btn-reset').addEventListener('click', () => this.resetBoard());

    const applyRulesBtn = document.getElementById('btn-apply-rules');
    if (applyRulesBtn) {
      applyRulesBtn.addEventListener('click', () => this.applyRulesFromCurrentState());
    }

    // Keybinds (Z for Undo, Y for Redo)
    document.addEventListener('keydown', (e) => {
      if (e.ctrlKey && e.key === 'z') {
        e.preventDefault();
        this.undo();
      } else if (e.ctrlKey && e.key === 'y') {
        e.preventDefault();
        this.redo();
      }
    });

    // Global drag end
    const endDrag = () => {
      if (this.isDragging) {
        this.isDragging = false;
        this.mouseHistory = []; // Clear history buffer on drag end
        if (this.currentDragGroup.length > 0) {
          this.undoStack.push(this.currentDragGroup);
          this.redoStack = []; // Clear redo stack on new action
          this.currentDragGroup = [];
          this.updateUndoRedoButtons();
          this.checkWinCondition();
        }
      }
    };
    window.addEventListener('mouseup', endDrag);
    window.addEventListener('touchend', endDrag);

    // Global mousemove for drag tracking
    this.svg.addEventListener('mousemove', (e) => {
      if (!this.isDragging) return;
      if (!this.mouseHistory) this.mouseHistory = [];
      this.mouseHistory.push({ x: e.clientX, y: e.clientY, time: Date.now() });
      if (this.mouseHistory.length > 40) {
        this.mouseHistory.shift();
      }
    });

    // Listeners for view reset and resizing
    const resetViewBtn = document.getElementById('btn-reset-view');
    if (resetViewBtn) {
      resetViewBtn.addEventListener('click', () => {
        this.hasManuallyAdjusted = false;
        this.fitBoardToContainer();
      });
    }
    window.addEventListener('resize', () => {
      if (!this.svgContainer) return;
      let containerW = this.svgContainer.clientWidth;
      let containerH = this.svgContainer.clientHeight;
      if (!containerW || !containerH) {
        const rect = this.svgContainer.getBoundingClientRect();
        containerW = rect.width;
        containerH = rect.height;
      }
      if (!containerW) containerW = window.innerWidth > 900 ? window.innerWidth - 400 : window.innerWidth - 48;
      if (!containerH) containerH = window.innerHeight * 0.6;

      const oldW = this.lastContainerW || containerW;
      const oldH = this.lastContainerH || containerH;
      this.lastContainerW = containerW;
      this.lastContainerH = containerH;

      if (containerW === oldW && containerH === oldH) {
        return;
      }

      if (this.hasManuallyAdjusted) {
        // Just adjust panning to keep center relative to the container resize,
        // do not reset zoom scale or pan to default.
        this.panX += (containerW - oldW) / 2;
        this.panY += (containerH - oldH) / 2;
        this.updateSVGTransform();
      } else {
        this.fitBoardToContainer();
      }
    });

    // Initialize custom board pan and zoom
    this.initPanZoom();
  }

  initPanZoom() {
    if (!this.svgContainer) return;

    // Desktop/Mouse Wheel Zoom
    this.svgContainer.addEventListener('wheel', (e) => {
      e.preventDefault();
      const rect = this.svgContainer.getBoundingClientRect();
      const px = e.clientX - rect.left;
      const py = e.clientY - rect.top;

      const zoomFactor = 1.1;
      let newScale = this.zoomScale;
      if (e.deltaY < 0) {
        newScale *= zoomFactor;
      } else {
        newScale /= zoomFactor;
      }
      newScale = Math.max(this.minZoom, Math.min(newScale, this.maxZoom));

      const factor = newScale / this.zoomScale;
      this.panX = px - (px - this.panX) * factor;
      this.panY = py - (py - this.panY) * factor;
      this.zoomScale = newScale;
      this.hasManuallyAdjusted = true;

      this.updateSVGTransform();
    }, { passive: false });

    // Desktop Mouse Drag Panning
    let isPanning = false;
    let startX = 0;
    let startY = 0;

    this.svgContainer.addEventListener('mousedown', (e) => {
      if (this.gameCompleted || this.isPaused) return;

      const isMiddleClick = e.button === 1;

      if (isMiddleClick) {
        isPanning = true;
        startX = e.clientX;
        startY = e.clientY;
        e.preventDefault();
        this.svgContainer.style.cursor = 'grabbing';
      }
    });

    window.addEventListener('mousemove', (e) => {
      if (!isPanning) return;
      const dx = e.clientX - startX;
      const dy = e.clientY - startY;
      this.panX += dx;
      this.panY += dy;
      this.hasManuallyAdjusted = true;
      startX = e.clientX;
      startY = e.clientY;
      this.updateSVGTransform();
    });

    window.addEventListener('mouseup', (e) => {
      if (isPanning) {
        isPanning = false;
        this.svgContainer.style.cursor = 'default';
      }
    });

    // Mobile/Touch zoom, pan and draw controls
    let touchMode = 'none'; // 'none', 'pinch', 'pan', 'draw', 'maybe_draw'
    let lastTouchDistance = 0;
    let lastTouchMidX = 0;
    let lastTouchMidY = 0;
    let lastTouchX = 0;
    let lastTouchY = 0;
    let touchStartX = 0;
    let touchStartY = 0;
    let touchDrawActive = false;
    let touchDrawState = 1;
    let touchDrawVisited = new Set();
    let longPressTimer = null;
    let startEdgeIdx = null;

    this.svgContainer.addEventListener('touchstart', (e) => {
      this.isTouchMode = true;

      if (e.touches.length === 2) {
        // Two-finger pinch zoom
        if (longPressTimer) {
          clearTimeout(longPressTimer);
          longPressTimer = null;
        }
        touchMode = 'pinch';
        touchDrawActive = false;
        this.currentDragGroup = []; // Cancel any active drawing

        const t1 = e.touches[0];
        const t2 = e.touches[1];
        lastTouchDistance = Math.hypot(t1.clientX - t2.clientX, t1.clientY - t2.clientY);
        lastTouchMidX = (t1.clientX + t2.clientX) / 2;
        lastTouchMidY = (t1.clientY + t2.clientY) / 2;

        e.preventDefault();
      } else if (e.touches.length === 1) {
        const touch = e.touches[0];

        // Prevent standard browser zoom/scroll/click emulation inside the container
        e.preventDefault();

        touchStartX = touch.clientX;
        touchStartY = touch.clientY;
        touchMode = 'maybe_draw';
        touchDrawActive = false;

        if (longPressTimer) {
          clearTimeout(longPressTimer);
        }

        const tapTolerance = Math.min(28, this.spacing * this.zoomScale * 0.45);
        startEdgeIdx = this.findClosestEdge(touch.clientX, touch.clientY, tapTolerance);

        longPressTimer = setTimeout(() => {
          if (touchMode === 'maybe_draw') {
            touchMode = 'draw';
            touchDrawActive = true;
            touchDrawVisited = new Set();
            this.currentDragGroup = [];

            if (navigator.vibrate) {
              navigator.vibrate(40);
            }

            if (startEdgeIdx !== null) {
              const currentState = this.edgeStates[startEdgeIdx];

              if (currentState === 1) {
                touchDrawState = 0; // Erase lines/crosses
              } else if (currentState === -1) {
                touchDrawState = -1; // Draw crosses
              } else {
                touchDrawState = 1; // Draw lines
              }

              this.isDragging = true;
              this.dragState = touchDrawState;
              this.applyEdgeStateChange(startEdgeIdx, touchDrawState);
              touchDrawVisited.add(startEdgeIdx);
            } else {
              touchDrawState = 1; // Default to line
              this.isDragging = true;
              this.dragState = touchDrawState;
            }

            this.lastMouseX = touch.clientX;
            this.lastMouseY = touch.clientY;
            this.mouseHistory = [{ x: touch.clientX, y: touch.clientY, time: Date.now() }];
            const startSVG = this.getSVGCoords(touch.clientX, touch.clientY);
            this.lastSVGX = startSVG.x;
            this.lastSVGY = startSVG.y;
          }
        }, 300);
      }
    }, { passive: false });

    this.svgContainer.addEventListener('touchmove', (e) => {
      if (this.gameCompleted || this.isPaused) return;

      if (touchMode === 'pinch' && e.touches.length === 2) {
        e.preventDefault();
        const t1 = e.touches[0];
        const t2 = e.touches[1];

        const dist = Math.hypot(t1.clientX - t2.clientX, t1.clientY - t2.clientY);
        const midX = (t1.clientX + t2.clientX) / 2;
        const midY = (t1.clientY + t2.clientY) / 2;

        let factor = dist / lastTouchDistance;
        let newScale = this.zoomScale * factor;
        newScale = Math.max(this.minZoom, Math.min(newScale, this.maxZoom));

        const rect = this.svgContainer.getBoundingClientRect();
        const px = midX - rect.left;
        const py = midY - rect.top;

        const scaleFactor = newScale / this.zoomScale;
        this.panX = px - (px - this.panX) * scaleFactor;
        this.panY = py - (py - this.panY) * scaleFactor;
        this.zoomScale = newScale;

        this.panX += (midX - lastTouchMidX);
        this.panY += (midY - lastTouchMidY);
        this.hasManuallyAdjusted = true;

        lastTouchDistance = dist;
        lastTouchMidX = midX;
        lastTouchMidY = midY;

        this.updateSVGTransform();
      } else if (e.touches.length === 1) {
        const touch = e.touches[0];
        const dx = touch.clientX - touchStartX;
        const dy = touch.clientY - touchStartY;
        const dist = Math.hypot(dx, dy);

        if (touchMode === 'maybe_draw') {
          // If we move before the long press timer fires, switch to panning!
          if (dist > 8) {
            if (longPressTimer) {
              clearTimeout(longPressTimer);
              longPressTimer = null;
            }
            touchMode = 'pan';
            lastTouchX = touch.clientX;
            lastTouchY = touch.clientY;
          }
        }

        if (touchMode === 'pan') {
          e.preventDefault();
          const panDx = touch.clientX - lastTouchX;
          const panDy = touch.clientY - lastTouchY;

          this.panX += panDx;
          this.panY += panDy;
          this.hasManuallyAdjusted = true;

          lastTouchX = touch.clientX;
          lastTouchY = touch.clientY;

          this.updateSVGTransform();
        } else if (touchMode === 'draw' && touchDrawActive) {
          e.preventDefault();

          if (!this.mouseHistory) this.mouseHistory = [];
          this.mouseHistory.push({ x: touch.clientX, y: touch.clientY, time: Date.now() });
          if (this.mouseHistory.length > 40) {
            this.mouseHistory.shift();
          }

          // Use fuzzy edge matching for drawing during dragging
          const dragTolerance = Math.min(24, this.spacing * this.zoomScale * 0.4);
          const edgeIdx = this.findClosestEdge(touch.clientX, touch.clientY, dragTolerance);
          if (edgeIdx !== null) {
            if (!touchDrawVisited.has(edgeIdx)) {
              touchDrawVisited.add(edgeIdx);
              this.isDragging = true;
              this.dragState = touchDrawState;
              this.handleEdgeDragEnter(edgeIdx, touch.clientX, touch.clientY);
            }
          }

          this.lastMouseX = touch.clientX;
          this.lastMouseY = touch.clientY;

          const localCoords = this.getSVGCoords(touch.clientX, touch.clientY);
          this.lastSVGX = localCoords.x;
          this.lastSVGY = localCoords.y;
        }
      }
    }, { passive: false });

    const handleTouchEnd = (e) => {
      if (longPressTimer) {
        clearTimeout(longPressTimer);
        longPressTimer = null;
      }

      if (touchMode === 'maybe_draw') {
        if (startEdgeIdx !== null) {
          e.preventDefault(); // Cancel emulated click/mousedown to prevent double trigger!
          this.handleEdgeClickTouch(startEdgeIdx);
        }
      } else if (touchMode === 'draw' && touchDrawActive) {
        touchDrawActive = false;
        this.isDragging = false;
        this.mouseHistory = [];

        if (this.currentDragGroup.length > 0) {
          this.undoStack.push(this.currentDragGroup);
          this.redoStack = [];
          this.currentDragGroup = [];
          this.updateUndoRedoButtons();
          this.checkWinCondition();
        }
      }
      touchMode = 'none';
    };

    this.svgContainer.addEventListener('touchend', handleTouchEnd, { passive: false });
    this.svgContainer.addEventListener('touchcancel', handleTouchEnd, { passive: false });
  }

  clampPanCoordinates() {
    if (!this.svgContainer) return;
    let containerW = this.svgContainer.clientWidth;
    let containerH = this.svgContainer.clientHeight;

    if (!containerW || !containerH) {
      const rect = this.svgContainer.getBoundingClientRect();
      containerW = rect.width;
      containerH = rect.height;
    }
    if (!containerW) containerW = window.innerWidth > 900 ? window.innerWidth - 400 : window.innerWidth - 48;
    if (!containerH) containerH = window.innerHeight * 0.6;

    const svgW = this.cols * this.spacing + this.padding * 2;
    const svgH = this.rows * this.spacing + this.padding * 2;

    const boardW = svgW * this.zoomScale;
    const boardH = svgH * this.zoomScale;

    const minX = Math.min(0, containerW - boardW);
    const maxX = Math.max(0, containerW - boardW);
    const minY = Math.min(0, containerH - boardH);
    const maxY = Math.max(0, containerH - boardH);

    this.panX = Math.max(minX, Math.min(this.panX, maxX));
    this.panY = Math.max(minY, Math.min(this.panY, maxY));
  }

  updateSVGTransform() {
    // Hardware accelerated transform instead of triggering expensive layout reflows with width/height updates
    if (this.transformRaf) return;
    this.transformRaf = requestAnimationFrame(() => {
      this.clampPanCoordinates();
      this.svg.style.transformOrigin = "0 0";
      this.svg.style.transform = `translate(${this.panX}px, ${this.panY}px) scale(${this.zoomScale})`;
      this.transformRaf = null;
    });
  }

  fitBoardToContainer() {
    if (!this.svgContainer) return;
    let containerW = this.svgContainer.clientWidth;
    let containerH = this.svgContainer.clientHeight;

    // Fallbacks if clientWidth/clientHeight are not ready (e.g. initial render)
    if (!containerW || !containerH) {
      const rect = this.svgContainer.getBoundingClientRect();
      containerW = rect.width;
      containerH = rect.height;
    }
    // Hard fallbacks to prevent returning early with zero values
    if (!containerW) containerW = window.innerWidth > 900 ? window.innerWidth - 400 : window.innerWidth - 48;
    if (!containerH) containerH = window.innerHeight * 0.6;

    const svgW = this.cols * this.spacing + this.padding * 2;
    const svgH = this.rows * this.spacing + this.padding * 2;

    // Use 0.95 margin ratio to minimize unnecessary empty spaces around the board
    const scaleX = (containerW * 0.95) / svgW;
    const scaleY = (containerH * 0.95) / svgH;
    const scale = Math.min(scaleX, scaleY);

    // Initial zoom fits the container completely by clamping only to this.minZoom.
    // Allow scaling up to 4.0 for nice large display on wide screens.
    this.zoomScale = Math.max(this.minZoom, Math.min(scale, 4.0));

    this.panX = (containerW - svgW * this.zoomScale) / 2;
    this.panY = (containerH - svgH * this.zoomScale) / 2;

    this.lastContainerW = containerW;
    this.lastContainerH = containerH;

    this.updateSVGTransform();
  }

  async handleFileUpload(e) {
    const file = e.target.files[0];
    if (!file) return;
    try {
      const text = await file.text();
      const lines = text.split(/\r?\n/).map(l => l.trim()).filter(l => l.length > 0);
      if (lines.length < 3) throw new Error("無効なフォーマットです。");

      const rows = parseInt(lines[0], 10);
      const cols = parseInt(lines[1], 10);

      const clues = [];
      for (let r = 0; r < rows; r++) {
        const rowClues = [];
        // Remove spaces so that '3 . 2' becomes '3.2'
        const rowStr = lines[2 + r] ? lines[2 + r].replace(/\s+/g, '') : "";
        if (rowStr.length < cols) throw new Error("行のデータが不足しています。");
        for (let c = 0; c < cols; c++) {
          const char = rowStr[c];
          if (char === '.') {
            rowClues.push(null);
          } else {
            rowClues.push(parseInt(char, 10));
          }
        }
        clues.push(rowClues);
      }

      let initialEdgeStates = null;
      let currentLineIdx = 2 + rows;
      if (lines.length >= currentLineIdx + (rows + 1) + rows) {
        const numH = (rows + 1) * cols;
        const numV = rows * (cols + 1);
        initialEdgeStates = new Int8Array(numH + numV);
        let hIdx = 0;
        for (let i = 0; i < rows + 1; i++) {
          const parts = lines[currentLineIdx++].trim().split(/\s+/);
          for (let j = 0; j < cols; j++) {
            initialEdgeStates[hIdx++] = parseInt(parts[j], 10) || 0;
          }
        }
        let vIdx = numH;
        for (let i = 0; i < rows; i++) {
          const parts = lines[currentLineIdx++].trim().split(/\s+/);
          for (let j = 0; j < cols + 1; j++) {
            initialEdgeStates[vIdx++] = parseInt(parts[j], 10) || 0;
          }
        }
      }

      this.statusTextEl.textContent = 'カスタム盤面の正解を計算中... ⚡';
      this.statusTextEl.classList.add('loading');

      // Let UI update
      setTimeout(() => {
        let solution = null;
        const numEdges = (rows + 1) * cols + rows * (cols + 1);

        if (window.wasmModule && typeof window.wasmModule._solve_puzzle_wasm === 'function') {
          window.wasmModule._init_grid(rows, cols);
          const cluesPtr = window.wasmModule._get_clues_ptr();
          const wasmCluesData = window.wasmModule.HEAP8.subarray(cluesPtr, cluesPtr + rows * cols);
          for (let r = 0; r < rows; r++) {
            for (let c = 0; c < cols; c++) {
              wasmCluesData[r * cols + c] = clues[r][c] === null ? -1 : clues[r][c];
            }
          }

          const foundCount = window.wasmModule._solve_puzzle_wasm(true, 5000000); // 5M steps for safety
          if (foundCount > 0) {
            const solPtr = window.wasmModule._get_solution_ptr(0);
            solution = new Int8Array(window.wasmModule.HEAP8.subarray(solPtr, solPtr + numEdges));
          }
        } else {
          // Fallback to JS solver if WASM is somehow not available
          const solver = new window.LoopCourseSolver(rows, cols, clues);
          const solutions = solver.solve(true, 100000);
          if (solutions && solutions.length > 0) {
            solution = solutions[0];
          }
        }

        if (!solution) {
          // If unresolvable or takes too long, provide a blank solution (hint won't work well)
          solution = new Int8Array(numEdges);
          console.warn("Could not find a solution for the loaded puzzle.");
        }

        this.loadCustomGame(rows, cols, clues, solution, initialEdgeStates);

        // Reset input to allow loading the same file again
        e.target.value = '';
      }, 50);

    } catch (err) {
      alert("ファイルの読み込みに失敗しました: " + err.message);
      e.target.value = '';
    }
  }

  goToLab() {
    const flatClues = [];
    if (Array.isArray(this.clues)) {
      for (let r = 0; r < this.rows; r++) {
        for (let c = 0; c < this.cols; c++) {
          const val = (this.clues[r] && this.clues[r][c] !== undefined) ? this.clues[r][c] : null;
          flatClues.push(val === null || val === undefined ? '.' : val);
        }
      }
    }
    const encoded = this.cols + 'x' + this.rows + '_' + flatClues.join('');
    localStorage.setItem('lab_custom_puzzle', JSON.stringify({
      rows: this.rows,
      cols: this.cols,
      clues: flatClues.map(c => c === '.' ? -1 : parseInt(c, 10)),
      time: Date.now()
    }));
    window.location.href = 'lab.html?p=' + encoded;
  }

  checkCustomPuzzleLoad() {
    const urlParams = new URLSearchParams(window.location.search);
    const pParam = urlParams.get('p');

    // 1. First priority: Direct URL Query Parameter (e.g. ?p=5x5_..2.11.1.1..3....12...2.1.)
    if (pParam && pParam.includes('_')) {
      try {
        const [dim, str] = pParam.split('_');
        const [cols, rows] = dim.split('x').map(Number);
        if (rows && cols && str && str.length >= rows * cols) {
          const clues2D = [];
          for (let r = 0; r < rows; r++) {
            const rowArr = [];
            for (let c = 0; c < cols; c++) {
              const char = str[r * cols + c];
              rowArr.push(char === '.' || char === '-' ? null : parseInt(char, 10));
            }
            clues2D.push(rowArr);
          }

          const selectEl = document.getElementById('select-size');
          if (selectEl) {
            const targetVal = cols + 'x' + rows;
            let hasOpt = false;
            for (let opt of selectEl.options) {
              if (opt.value === targetVal) { hasOpt = true; break; }
            }
            if (!hasOpt) {
              const newOpt = document.createElement('option');
              newOpt.value = targetVal;
              newOpt.textContent = `カスタム ${cols} x ${rows}`;
              selectEl.appendChild(newOpt);
            }
            selectEl.value = targetVal;
          }

          const numEdges = (rows + 1) * cols + rows * (cols + 1);
          let solution = new Int8Array(numEdges);

          if (window.wasmModule && typeof window.wasmModule._solve_puzzle_wasm === 'function') {
            window.wasmModule._init_grid(rows, cols);
            const cluesPtr = window.wasmModule._get_clues_ptr();
            const wasmCluesData = window.wasmModule.HEAP8.subarray(cluesPtr, cluesPtr + rows * cols);
            for (let r = 0; r < rows; r++) {
              for (let c = 0; c < cols; c++) {
                wasmCluesData[r * cols + c] = clues2D[r][c] === null ? -1 : clues2D[r][c];
              }
            }
            const foundCount = window.wasmModule._solve_puzzle_wasm(true, 5000000);
            if (foundCount > 0) {
              const solPtr = window.wasmModule._get_solution_ptr(0);
              solution = new Int8Array(window.wasmModule.HEAP8.subarray(solPtr, solPtr + numEdges));
            }
          }

          this.loadCustomGame(rows, cols, clues2D, solution);
          return true;
        }
      } catch (e) {
        console.error("Failed to parse URL query puzzle:", e);
      }
    }

    // 2. Second priority: localStorage backup
    const explicitCustom = urlParams.has('play');
    const stored = localStorage.getItem('lab_custom_puzzle');

    if (!stored && !explicitCustom) return false;

    try {
      if (!stored) return false;
      const data = JSON.parse(stored);
      if (data && data.rows && data.cols && Array.isArray(data.clues)) {
        const rows = data.rows;
        const cols = data.cols;
        const flatClues = data.clues;
        const hasNumbers = flatClues.some(c => c !== -1 && c !== null && c !== undefined);

        if (!explicitCustom && !hasNumbers) {
          return false;
        }

        const clues2D = [];
        for (let r = 0; r < rows; r++) {
          const rowArr = [];
          for (let c = 0; c < cols; c++) {
            const val = flatClues[r * cols + c];
            rowArr.push(val === -1 ? null : val);
          }
          clues2D.push(rowArr);
        }

        const selectEl = document.getElementById('select-size');
        if (selectEl) {
          const targetVal = cols + 'x' + rows;
          let hasOpt = false;
          for (let opt of selectEl.options) {
            if (opt.value === targetVal) { hasOpt = true; break; }
          }
          if (!hasOpt) {
            const newOpt = document.createElement('option');
            newOpt.value = targetVal;
            newOpt.textContent = `カスタム ${cols} x ${rows}`;
            selectEl.appendChild(newOpt);
          }
          selectEl.value = targetVal;
        }

        const numEdges = (rows + 1) * cols + rows * (cols + 1);
        let solution = new Int8Array(numEdges);

        if (window.wasmModule && typeof window.wasmModule._solve_puzzle_wasm === 'function') {
          window.wasmModule._init_grid(rows, cols);
          const cluesPtr = window.wasmModule._get_clues_ptr();
          const wasmCluesData = window.wasmModule.HEAP8.subarray(cluesPtr, cluesPtr + rows * cols);
          for (let r = 0; r < rows; r++) {
            for (let c = 0; c < cols; c++) {
              wasmCluesData[r * cols + c] = clues2D[r][c] === null ? -1 : clues2D[r][c];
            }
          }
          const foundCount = window.wasmModule._solve_puzzle_wasm(true, 5000000);
          if (foundCount > 0) {
            const solPtr = window.wasmModule._get_solution_ptr(0);
            solution = new Int8Array(window.wasmModule.HEAP8.subarray(solPtr, solPtr + numEdges));
          }
        }

        this.loadCustomGame(rows, cols, clues2D, solution);
        return true;
      }
    } catch (err) {
      console.error("Failed to load custom puzzle from storage:", err);
    }
    return false;
  }

  loadCustomGame(rows, cols, clues, solution, initialEdgeStates = null) {
    this.gameCompleted = false;
    this.resetHintFailedState();
    this.hasManuallyAdjusted = false;
    document.getElementById('victory-modal').classList.remove('active');

    if (this.generatorWorker) {
      this.generatorWorker.terminate();
      this.generatorWorker = null;
    }
    if (this.workerTimeoutTimer) {
      clearTimeout(this.workerTimeoutTimer);
      this.workerTimeoutTimer = null;
    }

    this.rows = rows;
    this.cols = cols;
    this.clues = clues;
    this.solution = solution;
    this.difficulty = "Custom";

    this.numH = (this.rows + 1) * this.cols;
    this.numV = this.rows * (this.cols + 1);
    this.numEdges = this.numH + this.numV;

    this.edgeStates = new Int8Array(this.numEdges);
    if (initialEdgeStates) {
      this.edgeStates.set(initialEdgeStates);
    }
    this.cellStates = new Int8Array(this.rows * this.cols);
    this.undoStack = [];
    this.redoStack = [];
    this.currentDragGroup = [];

    this.updateUndoRedoButtons();
    this.renderBoard();
    this.startTimer();
    this.scheduleAutoColoring();

    this.statusTextEl.innerHTML = 'パズル開始！線を引いて輪をつくりましょう';
    this.statusTextEl.classList.remove('loading');

    // Automatically apply 3x3 LUT deductions from WASM solver
    // this.applyWasmDeduction(rows, cols, clues); // Disabled per user request, but kept for future reference
  }

  applyWasmDeduction(rows, cols, clues) {
    if (!window.wasmModule || typeof window.wasmModule._init_grid !== 'function' || typeof window.wasmModule._applyStaticRules !== 'function') {
      console.warn("WASM module or _applyStaticRules not fully loaded, cannot apply static rules.");
      return;
    }

    try {
      window.wasmModule._init_grid(rows, cols);

      const cluesPtr = window.wasmModule._get_clues_ptr();
      const wasmCluesData = window.wasmModule.HEAP8.subarray(cluesPtr, cluesPtr + rows * cols);
      for (let r = 0; r < rows; r++) {
        for (let c = 0; c < cols; c++) {
          wasmCluesData[r * cols + c] = clues[r][c] === null ? -1 : clues[r][c];
        }
      }

      const edgesPtr = window.wasmModule._get_edge_states_ptr();
      const numH = (rows + 1) * cols;
      const numV = rows * (cols + 1);
      const numEdges = numH + numV;
      const wasmEdgeData = window.wasmModule.HEAP8.subarray(edgesPtr, edgesPtr + numEdges);
      for (let i = 0; i < numEdges; i++) {
        wasmEdgeData[i] = 0;
      }

      // Use _applyStaticRules directly
      const success = window.wasmModule._applyStaticRules();
      console.log("WASM applyStaticRules executed. Success:", success);

      let appliedCount = 0;
      for (let i = 0; i < numEdges; i++) {
        if (wasmEdgeData[i] !== 0) {
          this.edgeStates[i] = wasmEdgeData[i];
          appliedCount++;
        }
      }
      console.log(`Applied ${appliedCount} deduced edges from 3x3 LUT & global rules.`);

      this.scheduleAutoColoring();
      this.renderBoard();
    } catch (err) {
      console.error("Failed to run WASM deduction:", err);
    }
  }

  applyRulesFromCurrentState() {
    if (this.gameCompleted) return;
    if (!window.wasmModule || typeof window.wasmModule._init_grid !== 'function' || typeof window.wasmModule._deduct !== 'function') {
      console.warn("WASM module not fully loaded.");
      return;
    }

    try {
      window.wasmModule._init_grid(this.rows, this.cols);

      // Copy current clues
      const cluesPtr = window.wasmModule._get_clues_ptr();
      const wasmCluesData = window.wasmModule.HEAP8.subarray(cluesPtr, cluesPtr + this.rows * this.cols);
      for (let r = 0; r < this.rows; r++) {
        for (let c = 0; c < this.cols; c++) {
          wasmCluesData[r * this.cols + c] = this.clues[r][c] === null ? -1 : this.clues[r][c];
        }
      }

      const edgesPtr = window.wasmModule._get_edge_states_ptr();
      const numH = (this.rows + 1) * this.cols;
      const numV = this.rows * (this.cols + 1);
      const numEdges = numH + numV;
      const wasmEdgeData = window.wasmModule.HEAP8.subarray(edgesPtr, edgesPtr + numEdges);
      
      // Helper function to load current user edges into WASM
      const loadEdgesToWasm = () => {
        for (let i = 0; i < numEdges; i++) {
          wasmEdgeData[i] = this.edgeStates[i];
        }
      };

      // --- STEP 1: Apply Static Rules (All at once) ---
      loadEdgesToWasm();
      window.wasmModule._applyStaticRules();
      
      let staticChanges = [];
      for (let i = 0; i < numEdges; i++) {
        const oldState = this.edgeStates[i];
        const newState = wasmEdgeData[i];
        if (oldState === 0 && newState !== 0) {
          staticChanges.push({ edgeIdx: i, oldState: 0, newState: newState });
        }
      }

      if (staticChanges.length > 0) {
        this.applyRulesBatch(staticChanges, `✨ 定石ルールで ${staticChanges.length} 箇所を一括確定しました！`);
        return;
      }

      // --- STEP 2: Apply AC-3 (Exactly 1 move) ---
      loadEdgesToWasm();
      
      // Set the solver difficulty to match the current puzzle difficulty
      // For loaded/custom puzzles, force "Master" to enable full heuristics (Lookahead, etc.)
      const targetDiff = (this.difficulty === "Custom") ? "Master" : this.difficulty;
      if (typeof window.wasmModule.ccall === 'function') {
          window.wasmModule.ccall('set_solver_difficulty', 'void', ['string'], [targetDiff]);
      }
      
      // Tell WASM to defer GF2 processing until all other rules are exhausted
      if (typeof window.wasmModule._set_prioritize_gf2 === 'function') {
          window.wasmModule._set_prioritize_gf2(false);
      }
      
      window.wasmModule._deduct(); // Full AC-3 constraint propagation
      
      let foundChange = false;
      for (let i = 0; i < numEdges; i++) {
        if (this.edgeStates[i] === 0 && wasmEdgeData[i] !== 0) {
          foundChange = true;
          break;
        }
      }

      if (!foundChange) {
        if (typeof window.wasmModule._apply_lookahead_once === 'function') {
          console.log("No simple deductions found. Trying Lookahead...");
          const lookaheadFound = window.wasmModule._apply_lookahead_once();
          console.log("Lookahead returned:", lookaheadFound);
          if (lookaheadFound > 0) {
            foundChange = true;
          } else if (lookaheadFound === -1) {
            console.error("Lookahead returned -1! Contradiction in current board state.");
            this.statusTextEl.textContent = `盤面に矛盾が生じています！ルールを適用できません。`;
            this.statusTextEl.classList.remove('loading');
            return;
          }
        }
      }
      
      if (typeof window.wasmModule._get_first_deduced_edge === 'function' && foundChange) {
        const firstEdgeIdx = window.wasmModule._get_first_deduced_edge();
        if (firstEdgeIdx !== -1) {
          const newState = wasmEdgeData[firstEdgeIdx];
          const singleChange = [{ edgeIdx: firstEdgeIdx, oldState: 0, newState: newState }];
          
          let ruleName = "Unknown Rule";
          if (typeof window.wasmModule._get_first_deduced_rule_name === 'function' && typeof window.wasmModule.UTF8ToString === 'function') {
            const ptr = window.wasmModule._get_first_deduced_rule_name();
            if (ptr) {
                ruleName = window.wasmModule.UTF8ToString(ptr);
            }
          } else if (typeof window.wasmModule._get_last_applied_rule_name === 'function') {
            const ptr = window.wasmModule._get_last_applied_rule_name();
            if (ptr) {
                ruleName = window.wasmModule.UTF8ToString(ptr);
            }
          }

          // Count total changes found for the message
          let totalFound = 0;
          for (let i = 0; i < numEdges; i++) {
            if (this.edgeStates[i] === 0 && wasmEdgeData[i] !== 0) totalFound++;
          }
          
          this.applyRulesBatch(singleChange, `💡 1手確定: [${ruleName}] (残り候補: ${totalFound - 1})`);
          return;
        }
      } else if (foundChange) {
        // Fallback if WASM is not updated
        let ac3Changes = [];
        for (let i = 0; i < numEdges; i++) {
          const oldState = this.edgeStates[i];
          const newState = wasmEdgeData[i];
          if (oldState === 0 && newState !== 0) {
            ac3Changes.push({ edgeIdx: i, oldState: 0, newState: newState });
          }
        }
  
        if (ac3Changes.length > 0) {
          const singleChange = [ac3Changes[0]];
          this.applyRulesBatch(singleChange, `💡 推論で 1 箇所確定しました！ (残り候補: ${ac3Changes.length - 1})`);
          return;
        }
      }

      this.statusTextEl.textContent = `現在の盤面から自動確定できる箇所はありませんでした。`;
      console.log("No new rules could be applied from current state.");
    } catch (err) {
      console.error("Failed to apply rules:", err);
    }
  }

  applyRulesBatch(changes, statusMessage) {
    for (const change of changes) {
      this.edgeStates[change.edgeIdx] = change.newState;
      this.updateEdgeUI(change.edgeIdx);
    }

    this.undoStack.push(changes);
    this.redoStack = [];
    this.updateUndoRedoButtons();
    this.updateCluesHighlight();
    this.scheduleAutoColoring();
    this.checkWinCondition();
    
    this.statusTextEl.textContent = statusMessage;
    
    for (const change of changes) {
      const edgeGroup = this.edgeElements ? this.edgeElements[change.edgeIdx] : null;
      if (edgeGroup) {
        edgeGroup.classList.add('hint-pulse');
        setTimeout(() => {
          edgeGroup.classList.remove('hint-pulse');
        }, 1600);
      }
    }
  }

  startNewGame() {
    localStorage.removeItem('lab_custom_puzzle');
    if (window.history && window.history.replaceState) {
      window.history.replaceState(null, '', window.location.pathname);
    }
    this.gameCompleted = false;
    this.resetHintFailedState();
    this.hasManuallyAdjusted = false;
    document.getElementById('victory-modal').classList.remove('active');

    // Read current settings
    const sizeVal = document.getElementById('select-size').value; // "5x5", "7x7", "10x10"
    const [cols, rows] = sizeVal.split('x').map(Number);
    this.rows = rows;
    this.cols = cols;
    this.difficulty = document.getElementById('select-difficulty').value;

    // Show generating status
    this.statusTextEl.textContent = 'パズル作成中... (マルチスレッド実行中 ⚡)';
    this.statusTextEl.classList.add('loading');

    if (this.workerTimeoutTimer) {
      clearTimeout(this.workerTimeoutTimer);
      this.workerTimeoutTimer = null;
    }

    try {
      // Instantiate background Worker ONCE (Persistent Worker pattern)
      if (!this.generatorWorker) {
        this.generatorWorker = new Worker(`js/generator.worker.js?v=20260722_v2`);
      }

      // Set safety timeout to fallback to main-thread if worker crashes/stalls
      this.workerTimeoutTimer = setTimeout(() => {
        console.warn("Worker puzzle generation timed out. Falling back to main-thread...");
        if (this.generatorWorker) {
          this.generatorWorker.terminate();
          this.generatorWorker = null;
        }
        this.generateOnMainThread();
      }, 90000);

      this.generatorWorker.onmessage = (e) => {
        const data = e.data;
        if (data.type === 'progress') {
          // Reset safety timeout since progress is actively reported
          if (this.workerTimeoutTimer) {
            clearTimeout(this.workerTimeoutTimer);
          }
          this.workerTimeoutTimer = setTimeout(() => {
            console.warn("Worker puzzle generation timed out (stalled during progress). Falling back to main-thread...");
            if (this.generatorWorker) {
              this.generatorWorker.terminate();
              this.generatorWorker = null;
            }
            this.generateOnMainThread();
          }, 90000);

          if (data.total === -1) {
            this.statusTextEl.textContent = `パズル作成中... (初期盤面を探索中 ⚡: 試行 ${data.checked}回目)`;
          } else {
            const percent = Math.round((data.checked / data.total) * 100);
            this.statusTextEl.textContent = `パズル作成中... (ヒント最小化中 ⚡: ${percent}%)`;
          }
          return;
        }

        if (this.workerTimeoutTimer) {
          clearTimeout(this.workerTimeoutTimer);
          this.workerTimeoutTimer = null;
        }
        if (!data.success) {
          console.error("Worker puzzle generation failed:", data.error);
          this.statusTextEl.textContent = 'エラー：パズル生成に失敗しました。';
          this.statusTextEl.classList.remove('loading');
          return;
        }

        this.rows = data.rows;
        this.cols = data.cols;
        this.clues = data.clues;
        this.solution = data.solution;

        this.numH = (this.rows + 1) * this.cols;
        this.numV = this.rows * (this.cols + 1);
        this.numEdges = this.numH + this.numV;

        this.edgeStates = new Int8Array(this.numEdges);
        this.cellStates = new Int8Array(this.rows * this.cols);
        this.undoStack = [];
        this.redoStack = [];
        this.currentDragGroup = [];

        this.updateUndoRedoButtons();
        this.renderBoard();
        this.startTimer();
        this.scheduleAutoColoring();

        if (data.engineUsed === "WASM") {
          this.statusTextEl.innerHTML = '準備完了（<span class="engine-indicator wasm-engine">WASM高速エンジン ⚡</span>で非同期生成完了）！すべての数字を満たす1つのループを作ろう。';
        } else {
          this.statusTextEl.innerHTML = '準備完了（<span class="engine-indicator js-engine">JS互換エンジン ☕</span>で非同期生成完了）！すべての数字を満たす1つのループを作ろう。';
        }
        this.statusTextEl.classList.remove('loading');
      };

      // Trigger background thread puzzle generation on the persistent worker
      this.generatorWorker.postMessage({
        rows: this.rows,
        cols: this.cols,
        difficulty: this.difficulty
      });
    } catch (err) {
      console.warn("Web Worker creation failed (possibly running on local file:// or browser restriction). Falling back to main-thread:", err);
      this.generateOnMainThread();
    }
  }

  generateOnMainThread() {
    if (this.workerTimeoutTimer) {
      clearTimeout(this.workerTimeoutTimer);
      this.workerTimeoutTimer = null;
    }
    this.statusTextEl.textContent = 'パズル作成中... (メインスレッドで実行中 ⚡)';
    this.statusTextEl.classList.add('loading');

    // Small timeout to allow the browser UI to render the "パズル作成中" message
    setTimeout(() => {
      try {
        const generator = new LoopCourseGenerator(this.rows, this.cols);
        const puzzle = generator.generate(this.difficulty);

        this.rows = puzzle.rows;
        this.cols = puzzle.cols;
        this.clues = puzzle.clues;
        this.solution = puzzle.solution;

        this.numH = (this.rows + 1) * this.cols;
        this.numV = this.rows * (this.cols + 1);
        this.numEdges = this.numH + this.numV;

        this.edgeStates = new Int8Array(this.numEdges);
        this.cellStates = new Int8Array(this.rows * this.cols);
        this.undoStack = [];
        this.redoStack = [];
        this.currentDragGroup = [];

        this.updateUndoRedoButtons();
        this.renderBoard();
        this.startTimer();
        this.scheduleAutoColoring();

        if (puzzle.engineUsed === "WASM") {
          this.statusTextEl.innerHTML = '準備完了（<span class="engine-indicator wasm-engine">WASM高速エンジン ⚡</span>で生成完了）！すべての数字を満たす1つのループを作ろう。';
        } else {
          this.statusTextEl.innerHTML = '準備完了（<span class="engine-indicator js-engine">JS互換エンジン ☕</span>で生成完了）！すべての数字を満たす1つのループを作ろう。';
        }
        this.statusTextEl.classList.remove('loading');
      } catch (err) {
        console.error("Main-thread puzzle generation failed:", err);
        this.statusTextEl.textContent = 'エラー：パズル生成に失敗しました。';
        this.statusTextEl.classList.remove('loading');
      }
    }, 50);
  }

  renderBoard() {
    this.svg.innerHTML = '';

    // Cache cell and edge elements to avoid slow DOM queries during drag operations
    this.cellElements = Array.from({ length: this.rows }, () => new Array(this.cols).fill(null));
    this.cellBackgrounds = Array.from({ length: this.rows }, () => new Array(this.cols).fill(null));
    this.edgeElements = new Array(this.numEdges).fill(null);

    const svgWidth = this.cols * this.spacing + this.padding * 2;
    const svgHeight = this.rows * this.spacing + this.padding * 2;
    
    // Set base SVG size, scaling is handled purely by CSS transform for performance
    this.svg.style.width = `${svgWidth}px`;
    this.svg.style.height = `${svgHeight}px`;
    this.svg.setAttribute('width', svgWidth);
    this.svg.setAttribute('height', svgHeight);
    this.svg.setAttribute('viewBox', `0 0 ${svgWidth} ${svgHeight}`);

    // 1. Draw cell elements (backgrounds for all cells, clues where present)
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        const clue = this.clues[r][c];

        const cx = c * this.spacing + this.padding + this.spacing / 2;
        const cy = r * this.spacing + this.padding + this.spacing / 2;

        // Group for cell
        const cellGroup = document.createElementNS('http://www.w3.org/2000/svg', 'g');
        cellGroup.setAttribute('class', `cell-clue-group cell-${r}-${c}`);

        // Background subtle rect to show completed state or color marking
        const bg = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
        bg.setAttribute('x', c * this.spacing + this.padding + 2);
        bg.setAttribute('y', r * this.spacing + this.padding + 2);
        bg.setAttribute('width', this.spacing - 4);
        bg.setAttribute('height', this.spacing - 4);
        bg.setAttribute('rx', '6');
        bg.setAttribute('class', 'cell-bg');
        cellGroup.appendChild(bg);

        // Clue text (only if clue is not null)
        if (clue !== null) {
          const txt = document.createElementNS('http://www.w3.org/2000/svg', 'text');
          txt.setAttribute('x', cx);
          txt.setAttribute('y', cy + 6); // visual vertical alignment centering
          txt.setAttribute('text-anchor', 'middle');
          txt.setAttribute('class', 'clue-text');
          txt.textContent = clue;
          cellGroup.appendChild(txt);
        }

        this.svg.appendChild(cellGroup);

        // Store cellGroup and bg in cache
        this.cellElements[r][c] = cellGroup;
        this.cellBackgrounds[r][c] = bg;
      }
    }

    // 2. Draw Edges (Line and Cross representation, along with Wide Hitboxes for touch/clicks)
    const drawEdge = (edgeIdx, x1, y1, x2, y2, isHorizontal) => {
      const edgeGroup = document.createElementNS('http://www.w3.org/2000/svg', 'g');
      edgeGroup.setAttribute('class', `edge-group edge-${edgeIdx}`);
      edgeGroup.dataset.edgeIdx = edgeIdx;

      // A. Neon Line element
      const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
      line.setAttribute('x1', x1);
      line.setAttribute('y1', y1);
      line.setAttribute('x2', x2);
      line.setAttribute('y2', y2);
      line.setAttribute('class', 'grid-line');
      edgeGroup.appendChild(line);

      // B. Cross (×) element (shown when edge state is -1)
      const crossGroup = document.createElementNS('http://www.w3.org/2000/svg', 'g');
      crossGroup.setAttribute('class', 'cross-mark');
      const mx = (x1 + x2) / 2;
      const my = (y1 + y2) / 2;
      const cs = 5; // cross size half

      const c1 = document.createElementNS('http://www.w3.org/2000/svg', 'line');
      c1.setAttribute('x1', mx - cs);
      c1.setAttribute('y1', my - cs);
      c1.setAttribute('x2', mx + cs);
      c1.setAttribute('y2', my + cs);

      const c2 = document.createElementNS('http://www.w3.org/2000/svg', 'line');
      c2.setAttribute('x1', mx + cs);
      c2.setAttribute('y1', my - cs);
      c2.setAttribute('x2', mx - cs);
      c2.setAttribute('y2', my + cs);

      crossGroup.appendChild(c1);
      crossGroup.appendChild(c2);
      edgeGroup.appendChild(crossGroup);

      // C. Wide Transparent Hitbox for extremely smooth clicking/dragging
      const hitbox = document.createElementNS('http://www.w3.org/2000/svg', 'line');
      hitbox.setAttribute('x1', x1);
      hitbox.setAttribute('y1', y1);
      hitbox.setAttribute('x2', x2);
      hitbox.setAttribute('y2', y2);
      hitbox.setAttribute('class', 'edge-hitbox');
      hitbox.dataset.edgeIdx = edgeIdx;

      // Event listeners for dragging / clicking (PC Mouse / Fallback)
      hitbox.addEventListener('mousedown', (e) => {
        if (this.isTouchMode) return; // Ignore on touch screens
        this.handleEdgeMouseDown(e, edgeIdx);
      });
      hitbox.addEventListener('mouseenter', (e) => {
        if (this.isTouchMode) return; // Ignore on touch screens
        this.handleEdgeDragEnter(edgeIdx, e.clientX, e.clientY);
      });
      // Block right click context menu on the grid
      hitbox.addEventListener('contextmenu', (e) => e.preventDefault());

      edgeGroup.appendChild(hitbox);
      this.svg.appendChild(edgeGroup);

      // Store edgeGroup in cache
      this.edgeElements[edgeIdx] = edgeGroup;

      this.updateEdgeUI(edgeIdx);
    };

    // Draw all horizontal edges
    for (let r = 0; r <= this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        const edgeIdx = r * this.cols + c;
        const x1 = c * this.spacing + this.padding;
        const y1 = r * this.spacing + this.padding;
        const x2 = (c + 1) * this.spacing + this.padding;
        const y2 = y1;
        drawEdge(edgeIdx, x1, y1, x2, y2, true);
      }
    }

    // Draw all vertical edges
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c <= this.cols; c++) {
        const edgeIdx = this.numH + r * (this.cols + 1) + c;
        const x1 = c * this.spacing + this.padding;
        const y1 = r * this.spacing + this.padding;
        const x2 = x1;
        const y2 = (r + 1) * this.spacing + this.padding;
        drawEdge(edgeIdx, x1, y1, x2, y2, false);
      }
    }

    // 3. Draw Dots (vertexes) on top of the lines
    for (let r = 0; r <= this.rows; r++) {
      for (let c = 0; c <= this.cols; c++) {
        const dot = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
        dot.setAttribute('cx', c * this.spacing + this.padding);
        dot.setAttribute('cy', r * this.spacing + this.padding);
        dot.setAttribute('r', '4');
        dot.setAttribute('class', 'grid-dot');
        this.svg.appendChild(dot);
      }
    }

    // Initialize clue satisfying highlight
    this.updateCluesHighlight();
    this.fitBoardToContainer();
  }

  updateEdgeUI(edgeIdx) {
    const edgeGroup = this.edgeElements ? this.edgeElements[edgeIdx] : this.svg.querySelector(`.edge-${edgeIdx}`);
    if (!edgeGroup) return;

    const state = this.edgeStates[edgeIdx];

    // Toggle classes only if necessary (faster than remove/add)
    edgeGroup.classList.toggle('state-line', state === 1);
    edgeGroup.classList.toggle('state-cross', state === -1);
    edgeGroup.classList.toggle('state-empty', state === 0);
  }

  updateSingleClueHighlight(r, c) {
    if (r < 0 || r >= this.rows || c < 0 || c >= this.cols) return;
    const clue = this.clues[r][c];
    if (clue === null) return;

    const cellGroup = this.cellElements ? this.cellElements[r][c] : this.svg.querySelector(`.cell-${r}-${c}`);
    if (!cellGroup) return;

    const cellEdges = this.getCellEdges(r, c);
    const linesCount = cellEdges.reduce((sum, idx) => sum + (this.edgeStates[idx] === 1 ? 1 : 0), 0);
    const crossesCount = cellEdges.reduce((sum, idx) => sum + (this.edgeStates[idx] === -1 ? 1 : 0), 0);

    const isSatisfied = linesCount === clue;
    const isError = !isSatisfied && (linesCount > clue || crossesCount > (4 - clue));

    cellGroup.classList.toggle('clue-satisfied', isSatisfied);
    cellGroup.classList.toggle('clue-error', isError);
  }

  updateCluesHighlight() {
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        this.updateSingleClueHighlight(r, c);
      }
    }
  }

  scheduleAutoColoring() {
    if (this.coloringTimeout !== null) {
      cancelAnimationFrame(this.coloringTimeout);
    }
    this.coloringTimeout = requestAnimationFrame(() => {
      this.computeAutoColoring();
      this.coloringTimeout = null;
    });
  }

  computeAutoColoring() {
    if (!this.cellStates) return;

    // cellStates を初期化（0 = 外側/未着色、1 = 内側/青）
    this.cellStates.fill(0);

    if (!this.autoColorEnabled) {
      // 自動色塗りが無効の場合は、すべてのセルの表示をクリアして終了
      for (let r = 0; r < this.rows; r++) {
        for (let c = 0; c < this.cols; c++) {
          this.updateCellUI(r, c);
        }
      }
      return;
    }

    const numCells = this.rows * this.cols;
    const OUTSIDE = numCells;

    // cellColors 配列。-1 = 未確定, 0 = 外側, 1 = 内側
    const cellColors = new Int8Array(numCells + 1);
    cellColors.fill(-1);
    cellColors[OUTSIDE] = 0; // 外側領域は常に「外側 (0)」

    const queue = [OUTSIDE];
    let head = 0;

    while (head < queue.length) {
      const curr = queue[head++];
      const currColor = cellColors[curr];

      if (curr === OUTSIDE) {
        // 外周セルへの伝播
        // 1. 上端 (r = 0)
        for (let c = 0; c < this.cols; c++) {
          const edgeIdx = this.getHEdgeIndex(0, c);
          const state = this.edgeStates[edgeIdx];
          if (state === 1 || state === -1) {
            const cellIdx = 0 * this.cols + c;
            if (cellColors[cellIdx] === -1) {
              cellColors[cellIdx] = (state === 1) ? (1 - currColor) : currColor;
              queue.push(cellIdx);
            }
          }
        }
        // 2. 下端 (r = rows - 1)
        for (let c = 0; c < this.cols; c++) {
          const edgeIdx = this.getHEdgeIndex(this.rows, c);
          const state = this.edgeStates[edgeIdx];
          if (state === 1 || state === -1) {
            const cellIdx = (this.rows - 1) * this.cols + c;
            if (cellColors[cellIdx] === -1) {
              cellColors[cellIdx] = (state === 1) ? (1 - currColor) : currColor;
              queue.push(cellIdx);
            }
          }
        }
        // 3. 左端 (c = 0)
        for (let r = 0; r < this.rows; r++) {
          const edgeIdx = this.getVEdgeIndex(r, 0);
          const state = this.edgeStates[edgeIdx];
          if (state === 1 || state === -1) {
            const cellIdx = r * this.cols + 0;
            if (cellColors[cellIdx] === -1) {
              cellColors[cellIdx] = (state === 1) ? (1 - currColor) : currColor;
              queue.push(cellIdx);
            }
          }
        }
        // 4. 右端 (c = cols - 1)
        for (let r = 0; r < this.rows; r++) {
          const edgeIdx = this.getVEdgeIndex(r, this.cols);
          const state = this.edgeStates[edgeIdx];
          if (state === 1 || state === -1) {
            const cellIdx = r * this.cols + (this.cols - 1);
            if (cellColors[cellIdx] === -1) {
              cellColors[cellIdx] = (state === 1) ? (1 - currColor) : currColor;
              queue.push(cellIdx);
            }
          }
        }
      } else {
        // 盤面内セルの近傍への伝播
        const cr = Math.floor(curr / this.cols);
        const cc = curr % this.cols;

        const neighbors = [
          { nr: cr - 1, nc: cc, edgeIdx: this.getHEdgeIndex(cr, cc) },     // 上
          { nr: cr + 1, nc: cc, edgeIdx: this.getHEdgeIndex(cr + 1, cc) }, // 下
          { nr: cr, nc: cc - 1, edgeIdx: this.getVEdgeIndex(cr, cc) },     // 左
          { nr: cr, nc: cc + 1, edgeIdx: this.getVEdgeIndex(cr, cc + 1) }  // 右
        ];

        for (const adj of neighbors) {
          if (adj.nr >= 0 && adj.nr < this.rows && adj.nc >= 0 && adj.nc < this.cols) {
            const nextIdx = adj.nr * this.cols + adj.nc;
            if (cellColors[nextIdx] === -1) {
              const state = this.edgeStates[adj.edgeIdx];
              if (state === 1 || state === -1) {
                cellColors[nextIdx] = (state === 1) ? (1 - currColor) : currColor;
                queue.push(nextIdx);
              }
            }
          }
        }
      }
    }

    // 探索結果の反映（1 = 内側/青, 2 = 外側/赤, 0 = 未確定/色なし）
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        const cellIdx = r * this.cols + c;
        if (cellColors[cellIdx] === 1) {
          this.cellStates[cellIdx] = 1; // 1 = 内側 (青)
        } else if (cellColors[cellIdx] === 0) {
          this.cellStates[cellIdx] = 2; // 2 = 外側 (赤)
        } else {
          this.cellStates[cellIdx] = 0; // 0 = 未確定 (色なし)
        }
        this.updateCellUI(r, c);
      }
    }
  }

  updateCellUI(r, c) {
    const cellGroup = this.cellElements ? this.cellElements[r][c] : null;
    if (!cellGroup) return;
    const state = this.cellStates[r * this.cols + c];
    const isInside = state === 1;
    const isOutside = state === 2;

    cellGroup.classList.toggle('bg-color-a', isInside);
    cellGroup.classList.toggle('bg-color-b', isOutside);
  }

  handleEdgeMouseDown(e, edgeIdx) {
    if (this.gameCompleted || this.isPaused) return;

    // Only allow left click (0) and right click (2) for drawing
    if (e.button !== 0 && e.button !== 2) return;

    this.isDragging = true;
    this.lastMouseX = e.clientX;
    this.lastMouseY = e.clientY;
    this.mouseHistory = [{ x: e.clientX, y: e.clientY, time: Date.now() }];

    const startSVG = this.getSVGCoords(e.clientX, e.clientY);
    this.lastSVGX = startSVG.x;
    this.lastSVGY = startSVG.y;

    // Determine target state based on mouse button
    const isRightClick = e.button === 2;
    const currentState = this.edgeStates[edgeIdx];

    if (isRightClick) {
      this.dragState = (currentState === -1) ? 0 : -1;
    } else {
      // Left click
      this.dragState = (currentState === 1) ? 0 : 1;
    }

    this.applyEdgeStateChange(edgeIdx, this.dragState);
  }

  handleEdgeClickTouch(edgeIdx) {
    if (this.gameCompleted || this.isPaused) return;

    const currentState = this.edgeStates[edgeIdx];
    let newState = 0;

    // Cycle: Empty (0) -> Line (1) -> Cross (-1) -> Empty (0)
    if (currentState === 0) {
      newState = 1;
    } else if (currentState === 1) {
      newState = -1;
    } else {
      newState = 0;
    }

    if (currentState === newState) return; // No change

    this.applyEdgeStateChange(edgeIdx, newState);

    // Push to Undo stack as a single change step
    this.undoStack.push([{ edgeIdx, oldState: currentState, newState }]);
    this.redoStack = [];
    this.updateUndoRedoButtons();

    this.checkWinCondition();
  }

  handleEdgeDragEnter(edgeIdx, clientX = null, clientY = null) {
    if (!this.isDragging || this.gameCompleted || this.isPaused) return;

    // Prevent creating a branch (degree > 2) at endpoints during drag-drawing.
    // If the user wants to draw a branch/T-junction, they must explicitly click the edge.
    if (this.dragState === 1) {
      let r1, c1, r2, c2;
      const isVertical = edgeIdx >= this.numH;
      if (!isVertical) {
        r1 = Math.floor(edgeIdx / this.cols);
        c1 = edgeIdx % this.cols;
        r2 = r1;
        c2 = c1 + 1;
      } else {
        const vIdx = edgeIdx - this.numH;
        r1 = Math.floor(vIdx / (this.cols + 1));
        c1 = vIdx % (this.cols + 1);
        r2 = r1 + 1;
        c2 = c1;
      }

      if (this.countDrawnLinesForDot(r1, c1, edgeIdx) >= 2 || this.countDrawnLinesForDot(r2, c2, edgeIdx) >= 2) {
        return; // Block drawing this edge via drag as it would create a branch!
      }

      // Prevent drawing an edge if it would violate adjacent cell clues (lines count >= clue) during drag-drawing.
      const adjCells = this.getAdjacentCellsForEdge(edgeIdx);
      for (const cell of adjCells) {
        const clue = this.clues[cell.r][cell.c];
        if (clue !== null) {
          if (this.countDrawnLinesForCell(cell.r, cell.c, edgeIdx) >= clue) {
            return; // Block drawing this edge via drag as it would violate the cell's clue constraint!
          }
        }
      }
    }

    // Directional Lock to prevent accidental perpendicular line drawing
    // ONLY apply when drawing solid lines (dragState === 1). 
    // Allow players to drag freely when placing crosses (-1) or erasing (0).
    if (this.dragState === 1 && this.lastMouseX !== null && this.lastMouseY !== null && clientX !== null && clientY !== null) {
      const edge = this.getEdgeCoords(edgeIdx);
      const localCoords = this.getSVGCoords(clientX, clientY);

      let isIntentionalSwipe = false;
      if (edge.isVertical) {
        const distFromTop = localCoords.y - edge.y1;
        const distFromBottom = edge.y2 - localCoords.y;
        if (distFromTop > 11 && distFromBottom > 11) {
          isIntentionalSwipe = true;
        } else {
          // Corner Turn Bypass: if near a vertex, check if we are moving along the vertical axis of the edge
          const svgDy = localCoords.y - (this.lastSVGY !== undefined ? this.lastSVGY : localCoords.y);
          if (distFromTop <= 11 && svgDy > 0.3) {
            isIntentionalSwipe = true; // Moving downwards from top corner
          } else if (distFromBottom <= 11 && svgDy < -0.3) {
            isIntentionalSwipe = true; // Moving upwards from bottom corner
          }
        }
      } else {
        const distFromLeft = localCoords.x - edge.x1;
        const distFromRight = edge.x2 - localCoords.x;
        if (distFromLeft > 11 && distFromRight > 11) {
          isIntentionalSwipe = true;
        } else {
          // Corner Turn Bypass: if near a vertex, check if we are moving along the horizontal axis of the edge
          const svgDx = localCoords.x - (this.lastSVGX !== undefined ? this.lastSVGX : localCoords.x);
          if (distFromLeft <= 11 && svgDx > 0.3) {
            isIntentionalSwipe = true; // Moving right from left corner
          } else if (distFromRight <= 11 && svgDx < -0.3) {
            isIntentionalSwipe = true; // Moving left from right corner
          }
        }
      }

      // Only apply directional lock if it is NOT a deliberate mid-cell swipe
      if (!isIntentionalSwipe) {
        let dx = 0;
        let dy = 0;

        // Calculate high-fidelity instantaneous vector from recent history
        if (this.mouseHistory && this.mouseHistory.length > 1) {
          // Find the most recent point in history that is at least 12px away
          let basePoint = this.mouseHistory[this.mouseHistory.length - 1];
          for (let i = this.mouseHistory.length - 2; i >= 0; i--) {
            const p = this.mouseHistory[i];
            const dist = Math.hypot(clientX - p.x, clientY - p.y);
            if (dist >= 12) {
              basePoint = p;
              break;
            }
          }
          dx = clientX - basePoint.x;
          dy = clientY - basePoint.y;
        } else {
          // Fallback to static last successfully entered coordinates
          dx = clientX - this.lastMouseX;
          dy = clientY - this.lastMouseY;
        }

        // If the user drags mostly horizontally, block vertical edges
        if (edge.isVertical && Math.abs(dx) > 1.8 * Math.abs(dy) && Math.abs(dx) > 6) {
          return;
        }

        // If the user drags mostly vertically, block horizontal edges
        if (!edge.isVertical && Math.abs(dy) > 1.8 * Math.abs(dx) && Math.abs(dy) > 6) {
          return;
        }
      }
    }

    if (clientX !== null && clientY !== null) {
      this.lastMouseX = clientX;
      this.lastMouseY = clientY;

      const localCoords = this.getSVGCoords(clientX, clientY);
      this.lastSVGX = localCoords.x;
      this.lastSVGY = localCoords.y;
    }

    this.applyEdgeStateChange(edgeIdx, this.dragState);
  }

  getSVGCoords(clientX, clientY) {
    const pt = this.svg.createSVGPoint();
    pt.x = clientX;
    pt.y = clientY;
    const ctm = this.svg.getScreenCTM();
    if (ctm) {
      return pt.matrixTransform(ctm.inverse());
    }
    return { x: clientX, y: clientY }; // Fallback if CTM is not ready
  }

  findClosestEdge(clientX, clientY, maxDistance = 28) {
    if (!this.svg) return null;
    const ctm = this.svg.getScreenCTM();
    if (!ctm) return null;

    const svgCoords = this.getSVGCoords(clientX, clientY);
    const sx = svgCoords.x;
    const sy = svgCoords.y;

    const cCenter = Math.floor((sx - this.padding) / this.spacing);
    const rCenter = Math.floor((sy - this.padding) / this.spacing);

    const candidateEdges = new Set();
    const range = 2; // Check 2 cells radius around the touch point
    for (let r = rCenter - range; r <= rCenter + range; r++) {
      for (let c = cCenter - range; c <= cCenter + range; c++) {
        // Horizontal top/bottom
        const hTop = this.getHEdgeIndex(r, c);
        if (hTop !== -1) candidateEdges.add(hTop);
        const hBot = this.getHEdgeIndex(r + 1, c);
        if (hBot !== -1) candidateEdges.add(hBot);

        // Vertical left/right
        const vLeft = this.getVEdgeIndex(r, c);
        if (vLeft !== -1) candidateEdges.add(vLeft);
        const vRight = this.getVEdgeIndex(r, c + 1);
        if (vRight !== -1) candidateEdges.add(vRight);
      }
    }

    let closestEdgeIdx = null;
    let minDistance = Infinity;

    for (const edgeIdx of candidateEdges) {
      const coords = this.getEdgeCoords(edgeIdx);
      if (!coords) continue;

      // Map SVG coords to screen/client space using CTM
      const ex1 = coords.x1 * ctm.a + coords.y1 * ctm.c + ctm.e;
      const ey1 = coords.x1 * ctm.b + coords.y1 * ctm.d + ctm.f;
      const ex2 = coords.x2 * ctm.a + coords.y2 * ctm.c + ctm.e;
      const ey2 = coords.x2 * ctm.b + coords.y2 * ctm.d + ctm.f;

      // Distance from clientX, clientY to segment (ex1, ey1) -> (ex2, ey2)
      const dx = ex2 - ex1;
      const dy = ey2 - ey1;
      const l2 = dx * dx + dy * dy;
      let dist;
      if (l2 === 0) {
        dist = Math.hypot(clientX - ex1, clientY - ey1);
      } else {
        let t = ((clientX - ex1) * dx + (clientY - ey1) * dy) / l2;
        t = Math.max(0, Math.min(1, t));
        dist = Math.hypot(clientX - (ex1 + t * dx), clientY - (ey1 + t * dy));
      }

      if (dist < minDistance) {
        minDistance = dist;
        closestEdgeIdx = edgeIdx;
      }
    }

    if (minDistance <= maxDistance) {
      return closestEdgeIdx;
    }
    return null;
  }

  getEdgeCoords(edgeIdx) {
    const isVertical = edgeIdx >= this.numH;
    if (!isVertical) {
      // Horizontal edge
      const r = Math.floor(edgeIdx / this.cols);
      const c = edgeIdx % this.cols;
      const x1 = c * this.spacing + this.padding;
      const y1 = r * this.spacing + this.padding;
      const x2 = x1 + this.spacing;
      const y2 = y1;
      return { x1, y1, x2, y2, isVertical };
    } else {
      // Vertical edge
      const vIdx = edgeIdx - this.numH;
      const r = Math.floor(vIdx / (this.cols + 1));
      const c = vIdx % (this.cols + 1);
      const x1 = c * this.spacing + this.padding;
      const y1 = r * this.spacing + this.padding;
      const x2 = x1;
      const y2 = y1 + this.spacing;
      return { x1, y1, x2, y2, isVertical };
    }
  }

  getHEdgeIndex(r, c) {
    if (r < 0 || r > this.rows || c < 0 || c >= this.cols) return -1;
    return r * this.cols + c;
  }

  getVEdgeIndex(r, c) {
    if (r < 0 || r >= this.rows || c < 0 || c > this.cols) return -1;
    return this.numH + r * (this.cols + 1) + c;
  }

  getDotEdges(r, c) {
    const edges = [];
    // Up
    if (r > 0) edges.push(this.numH + (r - 1) * (this.cols + 1) + c);
    // Down
    if (r < this.rows) edges.push(this.numH + r * (this.cols + 1) + c);
    // Left
    if (c > 0) edges.push(r * this.cols + (c - 1));
    // Right
    if (c < this.cols) edges.push(r * this.cols + c);
    return edges;
  }

  countDrawnLinesForDot(r, c, excludeEdgeIdx) {
    const edges = this.getDotEdges(r, c);
    let count = 0;
    for (const idx of edges) {
      if (idx !== excludeEdgeIdx && this.edgeStates[idx] === 1) {
        count++;
      }
    }
    return count;
  }

  getCellEdges(r, c) {
    // Inlined for performance to avoid function overhead and bounds checks
    const top = r * this.cols + c;
    const right = this.numH + r * (this.cols + 1) + (c + 1);
    const bottom = (r + 1) * this.cols + c;
    const left = this.numH + r * (this.cols + 1) + c;
    return [top, right, bottom, left];
  }

  getAdjacentCellsForEdge(edgeIdx) {
    const cells = [];
    const isVertical = edgeIdx >= this.numH;
    if (!isVertical) {
      // Horizontal edge
      const r = Math.floor(edgeIdx / this.cols);
      const c = edgeIdx % this.cols;
      if (r > 0) cells.push({ r: r - 1, c }); // Top cell
      if (r < this.rows) cells.push({ r, c }); // Bottom cell
    } else {
      // Vertical edge
      const vIdx = edgeIdx - this.numH;
      const r = Math.floor(vIdx / (this.cols + 1));
      const c = vIdx % (this.cols + 1);
      if (c > 0) cells.push({ r, c: c - 1 }); // Left cell
      if (c < this.cols) cells.push({ r, c }); // Right cell
    }
    return cells;
  }

  countDrawnLinesForCell(r, c, excludeEdgeIdx) {
    const cellEdges = this.getCellEdges(r, c);
    let count = 0;
    for (const idx of cellEdges) {
      if (idx !== excludeEdgeIdx && this.edgeStates[idx] === 1) {
        count++;
      }
    }
    return count;
  }

  applyEdgeStateChange(edgeIdx, newState) {
    const oldState = this.edgeStates[edgeIdx];
    if (oldState === newState) return;
    this.resetHintFailedState();

    // Record state change for the current drag group (allows single Undo for entire drag line)
    // Avoid duplicate changes for same edge in one drag stroke
    if (this.isDragging) {
      const existingChangeIdx = this.currentDragGroup.findIndex(c => c.edgeIdx === edgeIdx);
      if (existingChangeIdx !== -1) {
        // Update new state, keep the original oldState from before the drag started
        this.currentDragGroup[existingChangeIdx].newState = newState;
      } else {
        this.currentDragGroup.push({ edgeIdx, oldState, newState });
      }
    }

    this.edgeStates[edgeIdx] = newState;
    this.updateEdgeUI(edgeIdx);

    // Performance optimization: only update highlights for adjacent cells (max 2) instead of the whole board
    const adjCells = this.getAdjacentCellsForEdge(edgeIdx);
    for (const cell of adjCells) {
      this.updateSingleClueHighlight(cell.r, cell.c);
    }
    this.scheduleAutoColoring();
  }

  undo() {
    if (this.undoStack.length === 0 || this.gameCompleted) return;
    this.resetHintFailedState();

    const changeGroup = this.undoStack.pop();
    const redoGroup = [];

    // Apply changes in reverse order
    for (let i = changeGroup.length - 1; i >= 0; i--) {
      const change = changeGroup[i];
      this.edgeStates[change.edgeIdx] = change.oldState;
      this.updateEdgeUI(change.edgeIdx);

      redoGroup.push({
        edgeIdx: change.edgeIdx,
        oldState: change.oldState,
        newState: change.newState
      });
    }

    this.redoStack.push(redoGroup.reverse());
    this.updateUndoRedoButtons();
    this.updateCluesHighlight();
    this.scheduleAutoColoring();
  }

  redo() {
    if (this.redoStack.length === 0 || this.gameCompleted) return;
    this.resetHintFailedState();

    const changeGroup = this.redoStack.pop();
    const undoGroup = [];

    for (const change of changeGroup) {
      this.edgeStates[change.edgeIdx] = change.newState;
      this.updateEdgeUI(change.edgeIdx);

      undoGroup.push({
        edgeIdx: change.edgeIdx,
        oldState: change.oldState,
        newState: change.newState
      });
    }

    this.undoStack.push(undoGroup);
    this.updateUndoRedoButtons();
    this.updateCluesHighlight();
    this.scheduleAutoColoring();
  }

  resetBoard() {
    if (this.gameCompleted) return;

    const changes = [];
    for (let i = 0; i < this.numEdges; i++) {
      if (this.edgeStates[i] !== 0) {
        changes.push({ edgeIdx: i, oldState: this.edgeStates[i], newState: 0 });
        this.edgeStates[i] = 0;
        this.updateEdgeUI(i);
      }
    }

    // Reset cell coloring states
    if (this.cellStates) {
      for (let i = 0; i < this.cellStates.length; i++) {
        this.cellStates[i] = 0;
      }
      for (let r = 0; r < this.rows; r++) {
        for (let c = 0; c < this.cols; c++) {
          this.updateCellUI(r, c);
        }
      }
    }

    if (changes.length > 0) {
      this.undoStack.push(changes);
      this.redoStack = [];
      this.updateUndoRedoButtons();
      this.updateCluesHighlight();
    }
  }

  resetHintFailedState() {
    this.hintFailedOnce = false;
    if (this.statusTextEl) {
      this.statusTextEl.classList.remove('status-blink');
    }
  }

  giveHint() {
    if (this.gameCompleted || this.isPaused) return;

    // Call LoopCourseHintSolver to find a logical hint based on current state
    const hint = LoopCourseHintSolver.getHint(
      this.rows,
      this.cols,
      this.clues,
      this.edgeStates,
      this.solution,
      true
    );

    if (hint) {
      this.resetHintFailedState();

      if (hint.isMulti) {
        const changes = [];
        for (const change of hint.changes) {
          const oldState = this.edgeStates[change.edgeIdx];
          this.edgeStates[change.edgeIdx] = change.state;
          this.updateEdgeUI(change.edgeIdx);
          changes.push({ edgeIdx: change.edgeIdx, oldState, newState: change.state });
        }
        this.updateCluesHighlight();
        this.scheduleAutoColoring();

        // Push all changes to Undo stack as a single change step
        this.undoStack.push(changes);
        this.redoStack = [];
        this.updateUndoRedoButtons();

        // Trigger golden pulsing glow animation on all hinted edges
        for (const change of hint.changes) {
          const edgeGroup = this.edgeElements ? this.edgeElements[change.edgeIdx] : this.svg.querySelector(`.edge-${change.edgeIdx}`);
          if (edgeGroup) {
            edgeGroup.classList.add('hint-pulse');
            setTimeout(() => {
              edgeGroup.classList.remove('hint-pulse');
            }, 1600);
          }
        }

        this.statusTextEl.textContent = `💡 ヒント：${hint.reason}`;
        this.checkWinCondition();
      } else {
        const hintIdx = hint.edgeIdx;
        const oldState = 0;
        const newState = hint.state; // 1 or -1

        this.edgeStates[hintIdx] = newState;
        this.updateEdgeUI(hintIdx);
        this.updateCluesHighlight();
        this.scheduleAutoColoring();

        // Push to Undo stack as a single change step
        this.undoStack.push([{ edgeIdx: hintIdx, oldState, newState }]);
        this.redoStack = [];
        this.updateUndoRedoButtons();

        // Trigger golden pulsing glow animation on the hinted edge
        const edgeGroup = this.edgeElements ? this.edgeElements[hintIdx] : this.svg.querySelector(`.edge-${hintIdx}`);
        if (edgeGroup) {
          edgeGroup.classList.add('hint-pulse');
          setTimeout(() => {
            edgeGroup.classList.remove('hint-pulse');
          }, 1600);
        }

        this.statusTextEl.textContent = `💡 ヒント：${hint.reason}`;
        this.checkWinCondition();
      }
    } else {
      // 4. If no logical hint was found, check if there are undecided edges
      const hasUndecided = Array.from(this.edgeStates).some(s => s === 0);
      if (hasUndecided) {
        if (!this.hintFailedOnce) {
          this.hintFailedOnce = true;
          this.statusTextEl.classList.add('status-blink');
          this.statusTextEl.textContent = '💡 定石を使用した確定ができませんでした。もう一度ヒントボタンを押すと、正答から1手開示します。';
        } else {
          // Reveal 1 correct move directly from solution
          let foundIdx = -1;

          // Find all dots that have exactly 1 line connected (disconnected line endpoints)
          const degree1Dots = [];
          for (let r = 0; r <= this.rows; r++) {
            for (let c = 0; c <= this.cols; c++) {
              const dotEdges = this.getDotEdges(r, c);
              let lineCount = 0;
              for (const e of dotEdges) {
                if (this.edgeStates[e] === 1) {
                  lineCount++;
                }
              }
              if (lineCount === 1) {
                degree1Dots.push({ r, c });
              }
            }
          }

          // Group 1: empty edges extending a degree-1 dot that is a line in the solution
          const group1CandidatesSet = new Set();
          for (const dot of degree1Dots) {
            const dotEdges = this.getDotEdges(dot.r, dot.c);
            for (const e of dotEdges) {
              if (this.edgeStates[e] === 0 && this.solution[e] === 1) {
                group1CandidatesSet.add(e);
              }
            }
          }
          const group1Candidates = Array.from(group1CandidatesSet);

          if (group1Candidates.length > 0) {
            // Select randomly from Group 1
            const rIdx = Math.floor(Math.random() * group1Candidates.length);
            foundIdx = group1Candidates[rIdx];
          }

          // Group 2: any empty edge that is a line in the solution
          if (foundIdx === -1) {
            const group2Candidates = [];
            for (let i = 0; i < this.numEdges; i++) {
              if (this.edgeStates[i] === 0 && this.solution[i] === 1) {
                group2Candidates.push(i);
              }
            }
            if (group2Candidates.length > 0) {
              const rIdx = Math.floor(Math.random() * group2Candidates.length);
              foundIdx = group2Candidates[rIdx];
            }
          }

          // Group 3: any empty edge (which will be a cross)
          if (foundIdx === -1) {
            const group3Candidates = [];
            for (let i = 0; i < this.numEdges; i++) {
              if (this.edgeStates[i] === 0) {
                group3Candidates.push(i);
              }
            }
            if (group3Candidates.length > 0) {
              const rIdx = Math.floor(Math.random() * group3Candidates.length);
              foundIdx = group3Candidates[rIdx];
            }
          }
          if (foundIdx !== -1) {
            const newState = this.solution[foundIdx];
            const oldState = 0;
            this.edgeStates[foundIdx] = newState;
            this.updateEdgeUI(foundIdx);
            this.updateCluesHighlight();
            this.scheduleAutoColoring();

            this.undoStack.push([{ edgeIdx: foundIdx, oldState, newState }]);
            this.redoStack = [];
            this.updateUndoRedoButtons();

            const edgeGroup = this.edgeElements ? this.edgeElements[foundIdx] : this.svg.querySelector(`.edge-${foundIdx}`);
            if (edgeGroup) {
              edgeGroup.classList.add('hint-pulse');
              setTimeout(() => {
                edgeGroup.classList.remove('hint-pulse');
              }, 1600);
            }

            this.resetHintFailedState();
            this.statusTextEl.textContent = '💡 手詰まりのため、正答から1手開示しました。';
            this.checkWinCondition();
          }
        }
      } else {
        this.resetHintFailedState();
        this.statusTextEl.textContent = '💡 すべての辺が入力されていますが、正しいループが完成していません。';
      }
    }
  }

  checkMistakes() {
    if (this.gameCompleted || this.isPaused) return;

    // 1. Check if there are any incorrectly placed edges (mistakes)
    const mistakes = [];
    for (let i = 0; i < this.numEdges; i++) {
      if (this.edgeStates[i] !== 0 && this.edgeStates[i] !== this.solution[i]) {
        mistakes.push(i);
      }
    }

    // 2. If there are mistakes, highlight them in red
    if (mistakes.length > 0) {
      mistakes.forEach(idx => {
        const edgeGroup = this.edgeElements ? this.edgeElements[idx] : this.svg.querySelector(`.edge-${idx}`);
        if (edgeGroup) {
          edgeGroup.classList.add('error-pulse');
          setTimeout(() => {
            edgeGroup.classList.remove('error-pulse');
          }, 1600);
        }
      });
      this.statusTextEl.textContent = `❌ 間違いが ${mistakes.length} 箇所あります（赤く点滅している線）。`;
    } else {
      // Find if player has drawn any lines at all
      const hasLines = Array.from(this.edgeStates).some(state => state !== 0);
      if (hasLines) {
        this.statusTextEl.textContent = '✅ 現在の線に間違いはありません！素晴らしい！';
      } else {
        this.statusTextEl.textContent = '✅ 盤面は空です。線を引き始めてみましょう。';
      }
    }
  }

  updateUndoRedoButtons() {
    this.undoBtn.disabled = this.undoStack.length === 0;
    this.redoBtn.disabled = this.redoStack.length === 0;
  }

  checkWinCondition() {
    // Reference global LoopCourseSolver
    const solver = new window.LoopCourseSolver(this.rows, this.cols, this.clues);
    solver.edgeStates = [...this.edgeStates];

    if (solver.isSolved()) {
      this.gameCompleted = true;
      this.stopTimer();
      this.triggerWinAnimation();
    }
  }

  triggerWinAnimation() {
    this.statusTextEl.textContent = '🎉 おめでとうございます！パズルが完成しました！';

    // Wave animation for the completed neon loop
    const lines = this.svg.querySelectorAll('.state-line');
    lines.forEach((line, i) => {
      line.style.animation = 'none';
      // force repaint
      void line.offsetWidth;
      line.style.animation = `neon-pulse 1.2s ease-in-out infinite alternate, win-wave 0.6s ease-in-out ${i * 0.03}s`;
    });

    // Display victory modal
    document.getElementById('modal-time').textContent = this.formatTime(this.secondsElapsed);
    document.getElementById('victory-modal').classList.add('active');
  }

  replayCurrentPuzzle() {
    document.getElementById('victory-modal').classList.remove('active');
    this.gameCompleted = false;
    this.edgeStates.fill(0);
    this.cellStates.fill(0);
    this.undoStack = [];
    this.redoStack = [];
    this.renderBoard();
    this.resetTimer();
    this.startTimer();
    this.statusTextEl.textContent = 'ゲーム再スタート！';
  }

  // Timer Management
  startTimer() {
    this.stopTimer();
    this.secondsElapsed = 0;
    this.timerEl.textContent = '00:00';
    this.isPaused = false;

    this.timerInterval = setInterval(() => {
      if (!this.isPaused && !this.gameCompleted) {
        this.secondsElapsed++;
        this.timerEl.textContent = this.formatTime(this.secondsElapsed);
      }
    }, 1000);
  }

  stopTimer() {
    if (this.timerInterval) {
      clearInterval(this.timerInterval);
      this.timerInterval = null;
    }
  }

  formatTime(totalSec) {
    const m = Math.floor(totalSec / 60).toString().padStart(2, '0');
    const s = (totalSec % 60).toString().padStart(2, '0');
    return `${m}:${s}`;
  }
}

// Bind to window for local file protocol compatibility without modules
window.LoopCourseGame = LoopCourseGame;

// Automatically bootstrap game on load
window.addEventListener('DOMContentLoaded', () => {
  window.game = new LoopCourseGame();
});
