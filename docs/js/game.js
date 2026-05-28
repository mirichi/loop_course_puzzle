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
    this.activeTool = 'pen'; // 'pen' or 'cross' or 'eraser'
    this.isDragging = false;
    this.dragState = 0; // State being painted: -1, 0, or 1
    
    // Timer
    this.timerInterval = null;
    this.secondsElapsed = 0;
    this.isPaused = false;
    this.gameCompleted = false;
    this.isTouchMode = false;
    
    // Layout parameters
    this.spacing = 54; // Distance between dots in px
    this.padding = 30; // Border padding in px
    
    this.initDOM();
    this.startNewGame();
  }

  initDOM() {
    this.svg = document.getElementById('game-svg');
    this.timerEl = document.getElementById('timer-value');
    this.statusTextEl = document.getElementById('status-text');
    this.undoBtn = document.getElementById('btn-undo');
    this.redoBtn = document.getElementById('btn-redo');
    
    // Setup event listeners for settings
    document.getElementById('btn-new-game').addEventListener('click', () => this.startNewGame());
    
    // Disable browser context menu on the entire board to allow smooth right-click tool usage
    this.svg.addEventListener('contextmenu', (e) => e.preventDefault());
    
    // Global board mousedown: initiate dragging even from empty spaces
    this.svg.addEventListener('mousedown', (e) => {
      if (this.gameCompleted || this.isPaused) return;
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
      if (isRightClick || this.activeTool === 'cross') {
        this.dragState = -1; // Cross
      } else if (this.activeTool === 'eraser') {
        this.dragState = 0; // Erase
      } else {
        this.dragState = 1; // Line
      }
    });

    // Detect touch interaction globally to switch to Mobile/Touch mode
    this.svg.addEventListener('touchstart', () => {
      this.isTouchMode = true;
    }, { passive: true });
    
    // Handle tool switching
    const toolBtns = document.querySelectorAll('.tool-btn');
    toolBtns.forEach(btn => {
      btn.addEventListener('click', (e) => {
        toolBtns.forEach(b => b.classList.remove('active'));
        const targetBtn = e.currentTarget;
        targetBtn.classList.add('active');
        this.activeTool = targetBtn.dataset.tool;
      });
    });
    
    // Undo / Redo
    this.undoBtn.addEventListener('click', () => this.undo());
    this.redoBtn.addEventListener('click', () => this.redo());
    document.getElementById('btn-hint').addEventListener('click', () => this.giveHint());
    document.getElementById('btn-reset').addEventListener('click', () => this.resetBoard());
    
    // Keybinds (Z for Undo, Y for Redo, Space to toggle tools)
    document.addEventListener('keydown', (e) => {
      if (e.ctrlKey && e.key === 'z') {
        e.preventDefault();
        this.undo();
      } else if (e.ctrlKey && e.key === 'y') {
        e.preventDefault();
        this.redo();
      } else if (e.key === '1') {
        document.querySelector('[data-tool="pen"]').click();
      } else if (e.key === '2') {
        document.querySelector('[data-tool="cross"]').click();
      } else if (e.key === '3') {
        document.querySelector('[data-tool="eraser"]').click();
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

    // (Touch dragging removed to enable browser default zoom and scroll)
  }

  startNewGame() {
    this.gameCompleted = false;
    document.getElementById('victory-modal').classList.remove('active');
    
    // Read current settings
    const sizeVal = document.getElementById('select-size').value; // "5x5", "7x7", "10x10"
    const [cols, rows] = sizeVal.split('x').map(Number);
    this.rows = rows;
    this.cols = cols;
    this.difficulty = document.getElementById('select-difficulty').value;
    
    // Show generating status
    this.statusTextEl.textContent = 'パズル作成中...';
    this.statusTextEl.classList.add('loading');
    
    // Use setTimeout so the DOM updates and shows "generating" before freezing for calculations
    setTimeout(() => {
      // Reference global LoopCourseGenerator
      const generator = new window.LoopCourseGenerator(this.rows, this.cols);
      const puzzle = generator.generate(this.difficulty);
      
      this.clues = puzzle.clues;
      this.solution = puzzle.solution;
      
      this.numH = (this.rows + 1) * this.cols;
      this.numV = this.rows * (this.cols + 1);
      this.numEdges = this.numH + this.numV;
      
      this.edgeStates = new Array(this.numEdges).fill(0);
      this.undoStack = [];
      this.redoStack = [];
      this.currentDragGroup = [];
      
      this.updateUndoRedoButtons();
      this.renderBoard();
      this.startTimer();
      
      this.statusTextEl.textContent = '準備完了！すべての数字を満たす1つのループを作ろう。';
      this.statusTextEl.classList.remove('loading');
    }, 50);
  }

  renderBoard() {
    this.svg.innerHTML = '';
    
    // Cache cell and edge elements to avoid slow DOM queries during drag operations
    this.cellElements = Array.from({ length: this.rows }, () => new Array(this.cols).fill(null));
    this.edgeElements = new Array(this.numEdges).fill(null);
    
    const svgWidth = this.cols * this.spacing + this.padding * 2;
    const svgHeight = this.rows * this.spacing + this.padding * 2;
    this.svg.setAttribute('width', svgWidth);
    this.svg.setAttribute('height', svgHeight);
    this.svg.setAttribute('viewBox', `0 0 ${svgWidth} ${svgHeight}`);
    
    // 1. Draw cell clues (numbers 0-3)
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        const clue = this.clues[r][c];
        if (clue === null) continue;
        
        const cx = c * this.spacing + this.padding + this.spacing / 2;
        const cy = r * this.spacing + this.padding + this.spacing / 2;
        
        // Group for numbers
        const cellGroup = document.createElementNS('http://www.w3.org/2000/svg', 'g');
        cellGroup.setAttribute('class', `cell-clue-group cell-${r}-${c}`);
        
        // Background subtle rect to show completed state
        const bg = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
        bg.setAttribute('x', c * this.spacing + this.padding + 2);
        bg.setAttribute('y', r * this.spacing + this.padding + 2);
        bg.setAttribute('width', this.spacing - 4);
        bg.setAttribute('height', this.spacing - 4);
        bg.setAttribute('rx', '6');
        bg.setAttribute('class', 'cell-bg');
        cellGroup.appendChild(bg);
        
        // Clue text
        const txt = document.createElementNS('http://www.w3.org/2000/svg', 'text');
        txt.setAttribute('x', cx);
        txt.setAttribute('y', cy + 6); // visual vertical alignment centering
        txt.setAttribute('text-anchor', 'middle');
        txt.setAttribute('class', 'clue-text');
        txt.textContent = clue;
        
        cellGroup.appendChild(txt);
        this.svg.appendChild(cellGroup);
        
        // Store cellGroup in cache
        this.cellElements[r][c] = cellGroup;
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
      
      // Touch coordinates tracking for fast mobile taps without 300ms delay
      let touchStartX = 0;
      let touchStartY = 0;
      let touchStartTime = 0;
      
      hitbox.addEventListener('touchstart', (e) => {
        this.isTouchMode = true;
        const touch = e.changedTouches[0];
        touchStartX = touch.clientX;
        touchStartY = touch.clientY;
        touchStartTime = Date.now();
      }, { passive: true });
      
      hitbox.addEventListener('touchend', (e) => {
        if (!this.isTouchMode) return;
        const touch = e.changedTouches[0];
        const dx = touch.clientX - touchStartX;
        const dy = touch.clientY - touchStartY;
        const dist = Math.hypot(dx, dy);
        const elapsed = Date.now() - touchStartTime;
        
        // If movement is negligible and duration is fast, it's a deliberate tap.
        // Process instantly and cancel emulated mouse events to bypass 300ms delay.
        if (dist < 6 && elapsed < 300) {
          e.preventDefault();
          this.handleEdgeClickTouch(edgeIdx);
        }
      }, { passive: false });
      
      // Event listeners for dragging / clicking (PC Mouse / Fallback)
      hitbox.addEventListener('mousedown', (e) => {
        if (this.isTouchMode) return; // Ignore on touch screens to allow default scroll/zoom
        this.handleEdgeMouseDown(e, edgeIdx);
      });
      hitbox.addEventListener('mouseenter', (e) => {
        if (this.isTouchMode) return; // Ignore on touch screens to allow default scroll/zoom
        this.handleEdgeDragEnter(edgeIdx, e.clientX, e.clientY);
      });
      hitbox.addEventListener('click', (e) => {
        if (!this.isTouchMode) return; // Only cycle states on touch devices
        this.handleEdgeClickTouch(edgeIdx);
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
  }

  updateEdgeUI(edgeIdx) {
    const edgeGroup = this.edgeElements ? this.edgeElements[edgeIdx] : this.svg.querySelector(`.edge-${edgeIdx}`);
    if (!edgeGroup) return;
    
    const state = this.edgeStates[edgeIdx];
    
    // Clear old state classes
    edgeGroup.classList.remove('state-line', 'state-cross', 'state-empty');
    
    if (state === 1) {
      edgeGroup.classList.add('state-line');
    } else if (state === -1) {
      edgeGroup.classList.add('state-cross');
    } else {
      edgeGroup.classList.add('state-empty');
    }
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
    
    cellGroup.classList.remove('clue-satisfied', 'clue-error');
    
    if (linesCount === clue) {
      cellGroup.classList.add('clue-satisfied');
    } else if (linesCount > clue || crossesCount > (4 - clue)) {
      cellGroup.classList.add('clue-error');
    }
  }

  updateCluesHighlight() {
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        this.updateSingleClueHighlight(r, c);
      }
    }
  }

  handleEdgeMouseDown(e, edgeIdx) {
    if (this.gameCompleted || this.isPaused) return;
    
    this.isDragging = true;
    this.lastMouseX = e.clientX;
    this.lastMouseY = e.clientY;
    this.mouseHistory = [{ x: e.clientX, y: e.clientY, time: Date.now() }];
    
    const startSVG = this.getSVGCoords(e.clientX, e.clientY);
    this.lastSVGX = startSVG.x;
    this.lastSVGY = startSVG.y;
    
    // Determine target state based on mouse button and active tools
    const isRightClick = e.button === 2;
    const currentState = this.edgeStates[edgeIdx];
    
    if (isRightClick || this.activeTool === 'cross') {
      this.dragState = (currentState === -1) ? 0 : -1;
    } else if (this.activeTool === 'eraser') {
      this.dragState = 0;
    } else {
      // Pen tool (normal left click)
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
    
    // Record state change for the current drag group (allows single Undo for entire drag line)
    // Avoid duplicate changes for same edge in one drag stroke
    const existingChangeIdx = this.currentDragGroup.findIndex(c => c.edgeIdx === edgeIdx);
    if (existingChangeIdx !== -1) {
      // Update new state, keep the original oldState from before the drag started
      this.currentDragGroup[existingChangeIdx].newState = newState;
    } else {
      this.currentDragGroup.push({ edgeIdx, oldState, newState });
    }
    
    this.edgeStates[edgeIdx] = newState;
    this.updateEdgeUI(edgeIdx);
    
    // Performance optimization: only update highlights for adjacent cells (max 2) instead of the whole board
    const adjCells = this.getAdjacentCellsForEdge(edgeIdx);
    for (const cell of adjCells) {
      this.updateSingleClueHighlight(cell.r, cell.c);
    }
  }

  undo() {
    if (this.undoStack.length === 0 || this.gameCompleted) return;
    
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
  }

  redo() {
    if (this.redoStack.length === 0 || this.gameCompleted) return;
    
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
    
    if (changes.length > 0) {
      this.undoStack.push(changes);
      this.redoStack = [];
      this.updateUndoRedoButtons();
      this.updateCluesHighlight();
    }
  }

  giveHint() {
    if (this.gameCompleted || this.isPaused) return;

    // 1. First, check if there are any incorrectly placed edges (mistakes)
    const mistakes = [];
    for (let i = 0; i < this.numEdges; i++) {
      if (this.edgeStates[i] !== 0 && this.edgeStates[i] !== this.solution[i]) {
        mistakes.push(i);
      }
    }

    // 2. If there are mistakes, highlight all of them in red and return early without changing the board
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
      this.statusTextEl.textContent = `❌ 間違いが ${mistakes.length} 箇所あります（赤く点滅している線）。まずはこれらを修正してください。`;
      return;
    }

    // 3. If there are no mistakes, look for undecided edges that should contain a LINE (solution === 1)
    const correctUndecidedLines = [];
    for (let i = 0; i < this.numEdges; i++) {
      if (this.edgeStates[i] === 0 && this.solution[i] === 1) {
        correctUndecidedLines.push(i);
      }
    }

    // 4. If we found an undecided correct line, reveal it as a solid line and pulse it in gold
    if (correctUndecidedLines.length > 0) {
      const hintIdx = correctUndecidedLines[Math.floor(Math.random() * correctUndecidedLines.length)];
      const oldState = 0;
      const newState = 1;

      this.edgeStates[hintIdx] = newState;
      this.updateEdgeUI(hintIdx);
      this.updateCluesHighlight();

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

      this.statusTextEl.textContent = '💡 ヒント適用！正しい線を1手確定しました。';
      this.checkWinCondition();
    } else {
      // 5. If there are no mistakes and no correct lines left to draw (the loop is fully complete)
      this.statusTextEl.textContent = '💡 すべての正しい線がすでに引かれています！クリア状態です！';
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
