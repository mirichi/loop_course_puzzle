/**
 * Loop Course Puzzle Hint Solver
 * Provides logic-based deduction (standard patterns) and contradiction-based look-ahead
 * to find the next logical move and explain it in Japanese.
 */
class LoopCourseHintSolver {
  constructor(rows, cols, clues, edgeStates, solution) {
    this.rows = rows;
    this.cols = cols;
    this.clues = clues; // 2D array of size rows x cols, with numbers 0-3 or null
    this.edgeStates = edgeStates; // Int8Array, 0 = empty, 1 = line, -1 = cross
    this.solution = solution; // Int8Array containing the correct solution

    this.numH = (rows + 1) * cols;
    this.numV = rows * (cols + 1);
    this.numEdges = this.numH + this.numV;
    this.numDots = (rows + 1) * (cols + 1);
  }

  getHEdgeIndex(r, c) {
    if (r < 0 || r > this.rows || c < 0 || c >= this.cols) return -1;
    return r * this.cols + c;
  }

  getVEdgeIndex(r, c) {
    if (r < 0 || r >= this.rows || c < 0 || c > this.cols) return -1;
    return this.numH + r * (this.cols + 1) + c;
  }

  // Returns array of 4 edge indices around cell (r, c) in clock-wise order: [top, right, bottom, left]
  getCellEdges(r, c) {
    const top = r * this.cols + c;
    const right = this.numH + r * (this.cols + 1) + (c + 1);
    const bottom = (r + 1) * this.cols + c;
    const left = this.numH + r * (this.cols + 1) + c;
    return [top, right, bottom, left];
  }

  // Returns array of up to 4 edge indices connected to dot (r, c)
  getDotEdges(r, c) {
    const edges = [];
    if (r > 0) edges.push(this.numH + (r - 1) * (this.cols + 1) + c); // Up
    if (r < this.rows) edges.push(this.numH + r * (this.cols + 1) + c); // Down
    if (c > 0) edges.push(r * this.cols + (c - 1)); // Left
    if (c < this.cols) edges.push(r * this.cols + c); // Right
    return edges;
  }

  // Helper to get the endpoints (dots) of an edge index
  getEdgeDots(edgeIdx) {
    if (edgeIdx < this.numH) {
      const r = Math.floor(edgeIdx / this.cols);
      const c = edgeIdx % this.cols;
      const dotA = r * (this.cols + 1) + c;
      const dotB = dotA + 1;
      return [dotA, dotB];
    } else {
      const vIdx = edgeIdx - this.numH;
      const r = Math.floor(vIdx / (this.cols + 1));
      const c = vIdx % (this.cols + 1);
      const dotA = r * (this.cols + 1) + c;
      const dotB = dotA + (this.cols + 1);
      return [dotA, dotB];
    }
  }

  // Helper to get the other endpoint of an edge given one endpoint
  getOtherDot(edgeIdx, dot) {
    const [dotA, dotB] = this.getEdgeDots(edgeIdx);
    if (dot === dotA) return dotB;
    if (dot === dotB) return dotA;
    return -1;
  }

  // BFS to check if dotA and dotB are already connected by lines
  // Returns path length if connected, -1 otherwise
  getLoopLengthIfClosed(dotA, dotB) {
    const visited = new Map(); // dot -> distance
    const queue = [dotA];
    visited.set(dotA, 0);

    while (queue.length > 0) {
      const curr = queue.shift();
      const dist = visited.get(curr);
      if (curr === dotB) {
        return dist + 1; // Path length + 1 (for the closing edge)
      }

      const r = Math.floor(curr / (this.cols + 1));
      const c = curr % (this.cols + 1);
      const edges = this.getDotEdges(r, c);

      for (const edgeIdx of edges) {
        if (this.edgeStates[edgeIdx] === 1) {
          const neighbor = this.getOtherDot(edgeIdx, curr);
          if (neighbor !== -1 && !visited.has(neighbor)) {
            visited.set(neighbor, dist + 1);
            queue.push(neighbor);
          }
        }
      }
    }
    return -1;
  }

  // Test if setting an edge state causes a contradiction using LoopCourseSolver
  testContradiction(edgeIdx, testState) {
    if (typeof LoopCourseSolver === 'undefined') {
      return false;
    }

    const tempSolver = new LoopCourseSolver(this.rows, this.cols, this.clues);
    tempSolver.edgeStates.set(this.edgeStates);
    tempSolver.dsuInitFromCurrent();
    tempSolver.clearQueues();

    const ok = tempSolver.setEdgeState(edgeIdx, testState);
    if (!ok) return true; // Direct contradiction

    const okProp = tempSolver.deductIncremental(3);
    if (!okProp) return true; // Contradiction during propagation

    return false;
  }

  // --- RULE 1: 格子角の3 (Corner 3) ---
  checkCorner3() {
    const corners = [
      { r: 0, c: 0, outerEdges: [this.getHEdgeIndex(0, 0), this.getVEdgeIndex(0, 0)] },
      { r: 0, c: this.cols - 1, outerEdges: [this.getHEdgeIndex(0, this.cols - 1), this.getVEdgeIndex(0, this.cols)] },
      { r: this.rows - 1, c: 0, outerEdges: [this.getHEdgeIndex(this.rows, 0), this.getVEdgeIndex(this.rows - 1, 0)] },
      { r: this.rows - 1, c: this.cols - 1, outerEdges: [this.getHEdgeIndex(this.rows, this.cols - 1), this.getVEdgeIndex(this.rows - 1, this.cols)] }
    ];

    const hints = [];
    for (const corner of corners) {
      if (this.clues[corner.r][corner.c] === 3) {
        for (const edgeIdx of corner.outerEdges) {
          if (this.edgeStates[edgeIdx] === 0) {
            hints.push({
              edgeIdx,
              state: 1,
              reason: `盤面の角にある3のマスの外側の辺は、必ず線になります。`
            });
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 13: 格子角の2 (Corner 2) ---
  checkCorner2() {
    const corners = [
      {
        r: 0, c: 0,
        extensions: [this.getHEdgeIndex(0, 1), this.getVEdgeIndex(1, 0)]
      },
      {
        r: 0, c: this.cols - 1,
        extensions: [this.getHEdgeIndex(0, this.cols - 2), this.getVEdgeIndex(1, this.cols)]
      },
      {
        r: this.rows - 1, c: 0,
        extensions: [this.getHEdgeIndex(this.rows, 1), this.getVEdgeIndex(this.rows - 2, 0)]
      },
      {
        r: this.rows - 1, c: this.cols - 1,
        extensions: [this.getHEdgeIndex(this.rows, this.cols - 2), this.getVEdgeIndex(this.rows - 2, this.cols)]
      }
    ];

    const hints = [];
    for (const corner of corners) {
      if (this.clues[corner.r][corner.c] === 2) {
        for (const edgeIdx of corner.extensions) {
          if (edgeIdx !== -1 && this.edgeStates[edgeIdx] === 0) {
            hints.push({
              edgeIdx,
              state: 1,
              reason: `角にある2はその両側の外周の辺（延長線）に必ず線が入ります。`
            });
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 2: 格子角の1 (Corner 1) ---
  checkCorner1() {
    const corners = [
      { r: 0, c: 0, outerEdges: [this.getHEdgeIndex(0, 0), this.getVEdgeIndex(0, 0)] },
      { r: 0, c: this.cols - 1, outerEdges: [this.getHEdgeIndex(0, this.cols - 1), this.getVEdgeIndex(0, this.cols)] },
      { r: this.rows - 1, c: 0, outerEdges: [this.getHEdgeIndex(this.rows, 0), this.getVEdgeIndex(this.rows - 1, 0)] },
      { r: this.rows - 1, c: this.cols - 1, outerEdges: [this.getHEdgeIndex(this.rows, this.cols - 1), this.getVEdgeIndex(this.rows - 1, this.cols)] }
    ];

    const hints = [];
    for (const corner of corners) {
      if (this.clues[corner.r][corner.c] === 1) {
        for (const edgeIdx of corner.outerEdges) {
          if (this.edgeStates[edgeIdx] === 0) {
            hints.push({
              edgeIdx,
              state: -1,
              reason: `盤面の角にある1のマスの外側の辺は、角の点に線が出入りできないため、×になります。`
            });
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 3: 隣接する3と3 (Adjacent 3s) ---
  checkAdjacent3s() {
    const hints = [];

    // Horizontal adjacents: cell (r, c) and (r, c + 1)
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols - 1; c++) {
        if (this.clues[r][c] === 3 && this.clues[r][c + 1] === 3) {
          const midV = this.getVEdgeIndex(r, c + 1);
          const leftV = this.getVEdgeIndex(r, c);
          const rightV = this.getVEdgeIndex(r, c + 2);

          // Lines
          if (this.edgeStates[midV] === 0) {
            hints.push({ edgeIdx: midV, state: 1, reason: `3のマスが横に隣り合っているため、2つの3の間の辺は線になります。` });
          }
          if (this.edgeStates[leftV] === 0) {
            hints.push({ edgeIdx: leftV, state: 1, reason: `3のマスが横に隣り合っているため、外側の平行な辺は線になります。` });
          }
          if (this.edgeStates[rightV] === 0) {
            hints.push({ edgeIdx: rightV, state: 1, reason: `3のマスが横に隣り合っているため、外側の平行な辺は線になります。` });
          }

          // Crosses (Extensions of the separating line at its endpoints)
          const extTop = this.getVEdgeIndex(r - 1, c + 1);
          const extBottom = this.getVEdgeIndex(r + 1, c + 1);
          if (extTop !== -1 && this.edgeStates[extTop] === 0) {
            hints.push({ edgeIdx: extTop, state: -1, reason: `3のマスが隣り合っているため、間の辺の延長線上は×になります。` });
          }
          if (extBottom !== -1 && this.edgeStates[extBottom] === 0) {
            hints.push({ edgeIdx: extBottom, state: -1, reason: `3のマスが隣り合っているため、間の辺の延長線上は×になります。` });
          }
        }
      }
    }

    // Vertical adjacents: cell (r, c) and (r + 1, c)
    for (let r = 0; r < this.rows - 1; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] === 3 && this.clues[r + 1][c] === 3) {
          const midH = this.getHEdgeIndex(r + 1, c);
          const topH = this.getHEdgeIndex(r, c);
          const bottomH = this.getHEdgeIndex(r + 2, c);

          // Lines
          if (this.edgeStates[midH] === 0) {
            hints.push({ edgeIdx: midH, state: 1, reason: `3のマスが縦に隣り合っているため、2つの3の間の辺は線になります。` });
          }
          if (this.edgeStates[topH] === 0) {
            hints.push({ edgeIdx: topH, state: 1, reason: `3のマスが縦に隣り合っているため、外側の平行な辺は線になります。` });
          }
          if (this.edgeStates[bottomH] === 0) {
            hints.push({ edgeIdx: bottomH, state: 1, reason: `3のマスが縦に隣り合っているため、外側の平行な辺は線になります。` });
          }

          // Crosses (Extensions of the separating line at its endpoints)
          const extLeft = this.getHEdgeIndex(r + 1, c - 1);
          const extRight = this.getHEdgeIndex(r + 1, c + 1);
          if (extLeft !== -1 && this.edgeStates[extLeft] === 0) {
            hints.push({ edgeIdx: extLeft, state: -1, reason: `3のマスが隣り合っているため、間の辺の延長線上は×になります。` });
          }
          if (extRight !== -1 && this.edgeStates[extRight] === 0) {
            hints.push({ edgeIdx: extRight, state: -1, reason: `3のマスが隣り合っているため、間の辺の延長線上は×になります。` });
          }
        }
      }
    }

    return hints;
  }

  // --- RULE 4: 対角の3と3 (Diagonal 3s) ---
  checkDiagonal3s() {
    const hints = [];

    for (let r = 0; r < this.rows - 1; r++) {
      for (let c = 0; c < this.cols - 1; c++) {
        // Case A: (r, c) and (r+1, c+1) are 3
        if (this.clues[r][c] === 3 && this.clues[r + 1][c + 1] === 3) {
          const top1 = this.getHEdgeIndex(r, c);
          const left1 = this.getVEdgeIndex(r, c);
          const bottom2 = this.getHEdgeIndex(r + 2, c + 1);
          const right2 = this.getVEdgeIndex(r + 1, c + 2);

          const edges = [top1, left1, bottom2, right2];
          for (const edgeIdx of edges) {
            if (this.edgeStates[edgeIdx] === 0) {
              hints.push({ edgeIdx, state: 1, reason: `3のマスが斜めに対角に隣り合っているため、それぞれの外側の角の2辺は必ず線になります。` });
            }
          }
        }

        // Case B: (r, c+1) and (r+1, c) are 3
        if (this.clues[r][c + 1] === 3 && this.clues[r + 1][c] === 3) {
          const top1 = this.getHEdgeIndex(r, c + 1);
          const right1 = this.getVEdgeIndex(r, c + 2);
          const bottom2 = this.getHEdgeIndex(r + 2, c);
          const left2 = this.getVEdgeIndex(r + 1, c);

          const edges = [top1, right1, bottom2, left2];
          for (const edgeIdx of edges) {
            if (this.edgeStates[edgeIdx] === 0) {
              hints.push({ edgeIdx, state: 1, reason: `3 of diagonal cells match corner edges logic.` });
              hints.push({ edgeIdx, state: 1, reason: `3のマスが斜めに対角に隣り合っているため、それぞれの外側の角の2辺は必ず線になります。` });
            }
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 5: 3と0の隣接 (3 adjacent to 0) ---
  check3AdjacentTo0() {
    const hints = [];
    const getAdjacents = (r, c) => [
      { r: r - 1, c, border: this.getHEdgeIndex(r, c) }, // Top
      { r, c: c + 1, border: this.getVEdgeIndex(r, c + 1) }, // Right
      { r: r + 1, c, border: this.getHEdgeIndex(r + 1, c) }, // Bottom
      { r, c: c - 1, border: this.getVEdgeIndex(r, c) }  // Left
    ];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] === 3) {
          const adjs = getAdjacents(r, c);
          for (const adj of adjs) {
            if (adj.r >= 0 && adj.r < this.rows && adj.c >= 0 && adj.c < this.cols) {
              if (this.clues[adj.r][adj.c] === 0) {
                // The other 3 edges of this '3' cell must be lines.
                const cellEdges = this.getCellEdges(r, c);
                for (const edgeIdx of cellEdges) {
                  if (edgeIdx !== adj.border && this.edgeStates[edgeIdx] === 0) {
                    hints.push({
                      edgeIdx,
                      state: 1,
                      reason: `3のマスが0のマスと隣り合っているため、接する辺は×になり、3のマスの残りの3辺はすべて線になります。`
                    });
                  }
                }
              }
            }
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 6: 0の周辺 (Around 0) ---
  checkAround0() {
    const hints = [];
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] === 0) {
          const cellEdges = this.getCellEdges(r, c);
          for (const edgeIdx of cellEdges) {
            if (this.edgeStates[edgeIdx] === 0) {
              hints.push({
                edgeIdx,
                state: -1,
                reason: `マスの数字が0なので、周囲 of cell is crossed out.`
              });
              hints.push({
                edgeIdx,
                state: -1,
                reason: `マスの数字が0なので、周囲の4つの辺はすべて×になります。`
              });
            }
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 7: マスの数字による確定 (Cell Clue Constraints) ---
  checkCellConstraints() {
    const hints = [];
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        const clue = this.clues[r][c];
        if (clue === null) continue;

        const cellEdges = this.getCellEdges(r, c);
        let lines = 0;
        let crosses = 0;
        const undecided = [];

        for (const edgeIdx of cellEdges) {
          if (this.edgeStates[edgeIdx] === 1) lines++;
          else if (this.edgeStates[edgeIdx] === -1) crosses++;
          else undecided.push(edgeIdx);
        }

        if (undecided.length > 0) {
          if (lines === clue) {
            for (const edgeIdx of undecided) {
              hints.push({
                edgeIdx,
                state: -1,
                reason: `マスの数字（${clue}）と同じ数（${lines}本）の線がすでに引かれているため、このマスの残りの辺は×になります。`
              });
            }
          } else if (crosses === 4 - clue) {
            for (const edgeIdx of undecided) {
              hints.push({
                edgeIdx,
                state: 1,
                reason: `マスの数字（${clue}）に対して、×がすでに${crosses}個あるため、残りの辺はすべて線になります。`
              });
            }
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 8: 点の接続ルール (Dot Degree Constraints) ---
  checkDotConstraints() {
    const hints = [];
    for (let r = 0; r <= this.rows; r++) {
      for (let c = 0; c <= this.cols; c++) {
        const dotEdges = this.getDotEdges(r, c);
        let lines = 0;
        let crosses = 0;
        const undecided = [];

        for (const edgeIdx of dotEdges) {
          if (this.edgeStates[edgeIdx] === 1) lines++;
          else if (this.edgeStates[edgeIdx] === -1) crosses++;
          else undecided.push(edgeIdx);
        }

        if (undecided.length > 0) {
          if (lines === 2) {
            for (const edgeIdx of undecided) {
              hints.push({
                edgeIdx,
                state: -1,
                reason: `点から引ける線は最大2本なので、すでに2本の線が接続しているこの点の残りの辺は×になります。`
              });
            }
          } else if (lines === 1 && undecided.length === 1) {
            hints.push({
              edgeIdx: undecided[0],
              state: 1,
              reason: `線は途中で途切れてはいけないため、この点から伸びる線は残された最後の辺へと進みます。`
            });
          } else if (lines === 0 && undecided.length === 1) {
            hints.push({
              edgeIdx: undecided[0],
              state: -1,
              reason: `この点に接続する辺が1本しか残っておらず、そこに線を引くと行き止まりになってしまうため、×になります。`
            });
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 9: 小ループの回避 (Avoid Premature Loops) ---
  checkPrematureLoops() {
    const hints = [];
    const totalDrawn = this.edgeStates.reduce((sum, s) => sum + (s === 1 ? 1 : 0), 0);
    const totalSolutionLines = this.solution ? this.solution.reduce((sum, s) => sum + (s === 1 ? 1 : 0), 0) : 0;

    for (let i = 0; i < this.numEdges; i++) {
      if (this.edgeStates[i] === 0) {
        const [dotA, dotB] = this.getEdgeDots(i);
        const loopLen = this.getLoopLengthIfClosed(dotA, dotB);
        if (loopLen > 0) {
          let isPremature = false;
          if (totalSolutionLines > 0 && loopLen < totalSolutionLines) {
            isPremature = true;
          } else if (loopLen < totalDrawn + 1) {
            isPremature = true;
          }

          if (isPremature) {
            hints.push({
              edgeIdx: i,
              state: -1,
              reason: `ここに線を引くと、全体のループが完成する前に小さなループが閉じてしまうため、×になります。`
            });
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 14: 3の角の外側にxが2つある場合の定石 (3 Corner Outside Crosses) ---
  check3CornerOutsideCrosses() {
    const hints = [];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 3) continue;

        const cellHtop = this.getHEdgeIndex(r, c);
        const cellHbottom = this.getHEdgeIndex(r + 1, c);
        const cellVleft = this.getVEdgeIndex(r, c);
        const cellVright = this.getVEdgeIndex(r, c + 1);

        const corners = [
          {
            name: '左上',
            outside: [
              this.getVEdgeIndex(r - 1, c),
              this.getHEdgeIndex(r, c - 1)
            ],
            inside: [cellHtop, cellVleft]
          },
          {
            name: '右上',
            outside: [
              this.getVEdgeIndex(r - 1, c + 1),
              this.getHEdgeIndex(r, c + 1)
            ],
            inside: [cellHtop, cellVright]
          },
          {
            name: '左下',
            outside: [
              this.getVEdgeIndex(r + 1, c),
              this.getHEdgeIndex(r + 1, c - 1)
            ],
            inside: [cellHbottom, cellVleft]
          },
          {
            name: '右下',
            outside: [
              this.getVEdgeIndex(r + 1, c + 1),
              this.getHEdgeIndex(r + 1, c + 1)
            ],
            inside: [cellHbottom, cellVright]
          }
        ];

        for (const corner of corners) {
          const isCross = (edgeIdx) => {
            if (edgeIdx === -1) return true; // Out of bounds is treated as cross
            return this.edgeStates[edgeIdx] === -1;
          };

          if (isCross(corner.outside[0]) && isCross(corner.outside[1])) {
            for (const inEdge of corner.inside) {
              if (this.edgeStates[inEdge] === 0) {
                hints.push({
                  edgeIdx: inEdge,
                  state: 1,
                  reason: `3のマスの${corner.name}の角から外へ伸びる2つの辺が×（または盤面外）のため、その角を構成するマスの2辺は必ず線になります。`
                });
              }
            }
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 15: 2の角の外側にxが2つある場合の定石 (2 Corner Outside Crosses) ---
  check2CornerOutsideCrosses() {
    const hints = [];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 2) continue;

        const corners = [
          {
            id: 0, // TL
            name: '左上',
            outside: [
              this.getVEdgeIndex(r - 1, c), // Up
              this.getHEdgeIndex(r, c - 1)  // Left
            ],
            oppositeId: 3, // BR
            adjacentIds: [1, 2] // TR, BL
          },
          {
            id: 1, // TR
            name: '右上',
            outside: [
              this.getVEdgeIndex(r - 1, c + 1), // Up
              this.getHEdgeIndex(r, c + 1)      // Right
            ],
            oppositeId: 2, // BL
            adjacentIds: [0, 3] // TL, BR
          },
          {
            id: 2, // BL
            name: '左下',
            outside: [
              this.getVEdgeIndex(r + 1, c),     // Down
              this.getHEdgeIndex(r + 1, c - 1)  // Left
            ],
            oppositeId: 1, // TR
            adjacentIds: [0, 3] // TL, BR
          },
          {
            id: 3, // BR
            name: '右下',
            outside: [
              this.getVEdgeIndex(r + 1, c + 1), // Down
              this.getHEdgeIndex(r + 1, c + 1)  // Right
            ],
            oppositeId: 0, // TL
            adjacentIds: [1, 2] // TR, BL
          }
        ];

        const isCross = (edgeIdx) => {
          if (edgeIdx === -1) return true; // Out of bounds is treated as cross
          return this.edgeStates[edgeIdx] === -1;
        };

        for (let i = 0; i < 4; i++) {
          const base = corners[i];
          // If base corner has 2 outside crosses
          if (isCross(base.outside[0]) && isCross(base.outside[1])) {
            
            // 1. Opposite corner cross deduction (xの確定)
            const opp = corners[base.oppositeId];
            const oppOut0 = opp.outside[0];
            const oppOut1 = opp.outside[1];
            const s0 = oppOut0 === -1 ? -1 : this.edgeStates[oppOut0];
            const s1 = oppOut1 === -1 ? -1 : this.edgeStates[oppOut1];

            if (s0 === -1 && s1 === 0 && oppOut1 !== -1) {
              hints.push({
                edgeIdx: oppOut1,
                state: -1,
                reason: `2のマスの${base.name}の角の外側に×が2つあり、対角の${opp.name}の角の外側も片方が×になっているため、もう一方の辺は×になります。`
              });
            } else if (s1 === -1 && s0 === 0 && oppOut0 !== -1) {
              hints.push({
                edgeIdx: oppOut0,
                state: -1,
                reason: `2のマスの${base.name}の角の外側に×が2つあり、対角の${opp.name}の角の外側も片方が×になっているため、もう一方の辺は×になります。`
              });
            }

            // 2. Adjacent corners line deduction (線の確定) & cross deduction (xの確定)
            for (const adjId of base.adjacentIds) {
              const adj = corners[adjId];
              const adjOut0 = adj.outside[0];
              const adjOut1 = adj.outside[1];
              const a0 = adjOut0 === -1 ? -1 : this.edgeStates[adjOut0];
              const a1 = adjOut1 === -1 ? -1 : this.edgeStates[adjOut1];

              // Line deductions (when one outside edge is cross)
              if (a0 === -1 && a1 === 0 && adjOut1 !== -1) {
                hints.push({
                  edgeIdx: adjOut1,
                  state: 1,
                  reason: `2のマスの${base.name}の角の外側に×が2つあり、隣の${adj.name}の角の外側の片方が×になっているため、もう一方の辺には必ず線が入ります。`
                });
              } else if (a1 === -1 && a0 === 0 && adjOut0 !== -1) {
                hints.push({
                  edgeIdx: adjOut0,
                  state: 1,
                  reason: `2のマスの${base.name}の角の外側に×が2つあり、隣の${adj.name}の角の外側の片方が×になっているため、もう一方の辺には必ず線が入ります。`
                });
              }

              // Cross deductions (when one outside edge is line)
              if (a0 === 1 && a1 === 0 && adjOut1 !== -1) {
                hints.push({
                  edgeIdx: adjOut1,
                  state: -1,
                  reason: `2のマスの${base.name}の角の外側に×が2つあり、隣の${adj.name}の角に外から線が入ってきたため、もう一方の辺は×になります。`
                });
              } else if (a1 === 1 && a0 === 0 && adjOut0 !== -1) {
                hints.push({
                  edgeIdx: adjOut0,
                  state: -1,
                  reason: `2のマスの${base.name}の角の外側に×が2つあり、隣の${adj.name}の角に外から線が入ってきたため、もう一方の辺は×になります。`
                });
              }
            }
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 22: Adjacent 1s with Diagonal Crosses (Adjacent 1s Line Propagation) ---
  checkAdjacent1sLinePropagation() {
    const hints = [];

    // Helper to check if a cell's corner (defined by its 2 edges) is blocked by crosses
    const isCornerBlocked = (edgeA, edgeB) => {
      // Out of bounds is treated as cross (-1)
      const stateA = edgeA === -1 ? -1 : this.edgeStates[edgeA];
      const stateB = edgeB === -1 ? -1 : this.edgeStates[edgeB];
      return stateA === -1 && stateB === -1;
    };

    // 1. Vertically adjacent 1s
    for (let r = 0; r < this.rows - 1; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] === 1 && this.clues[r + 1][c] === 1) {
          const rBoundary = r + 1;
          const leftH = this.getHEdgeIndex(rBoundary, c - 1);
          const rightH = this.getHEdgeIndex(rBoundary, c + 1);

          // Get corner edges of top cell
          const topTL_L = this.getVEdgeIndex(r, c);
          const topTL_T = this.getHEdgeIndex(r, c);
          const topTR_R = this.getVEdgeIndex(r, c + 1);
          const topTR_T = this.getHEdgeIndex(r, c);

          // Get corner edges of bottom cell
          const botBL_L = this.getVEdgeIndex(r + 1, c);
          const botBL_B = this.getHEdgeIndex(r + 2, c);
          const botBR_R = this.getVEdgeIndex(r + 1, c + 1);
          const botBR_B = this.getHEdgeIndex(r + 2, c);

          // Case 1.1: TR of top cell is blocked (H(r,c) and V(r,c+1) are crosses)
          // AND BL of bottom cell is blocked (H(r+2,c) and V(r+1,c) are crosses)
          const blocked1 = isCornerBlocked(topTR_T, topTR_R) && isCornerBlocked(botBL_B, botBL_L);

          // Case 1.2: TL of top cell is blocked (H(r,c) and V(r,c) are crosses)
          // AND BR of bottom cell is blocked (H(r+2,c) and V(r+1,c+1) are crosses)
          const blocked2 = isCornerBlocked(topTL_T, topTL_L) && isCornerBlocked(botBR_B, botBR_R);

          if (blocked1 || blocked2) {
            // Line propagation:
            // If right edge rightH is line (1), then left edge leftH must be line (1)
            if (rightH !== -1 && this.edgeStates[rightH] === 1) {
              if (leftH !== -1 && this.edgeStates[leftH] === 0) {
                hints.push({
                  edgeIdx: leftH,
                  state: 1,
                  reason: `縦に並ぶ2つの1のマスにおいて、対角の角が×で塞がれており、右から線が入ってきたため、左側の辺は必ず線になります。`
                });
              }
            }
            // If left edge leftH is line (1), then right edge rightH must be line (1)
            if (leftH !== -1 && this.edgeStates[leftH] === 1) {
              if (rightH !== -1 && this.edgeStates[rightH] === 0) {
                hints.push({
                  edgeIdx: rightH,
                  state: 1,
                  reason: `縦に並ぶ2つの1のマスにおいて、対角の角が×で塞がれており、左から線が入ってきたため、右側の辺は必ず線になります。`
                });
              }
            }
          }
        }
      }
    }

    // 2. Horizontally adjacent 1s
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols - 1; c++) {
        if (this.clues[r][c] === 1 && this.clues[r][c + 1] === 1) {
          const cBoundary = c + 1;
          const topV = this.getVEdgeIndex(r - 1, cBoundary);
          const bottomV = this.getVEdgeIndex(r + 1, cBoundary);

          // Get corner edges of left cell
          const leftTL_T = this.getHEdgeIndex(r, c);
          const leftTL_L = this.getVEdgeIndex(r, c);
          const leftBL_B = this.getHEdgeIndex(r + 1, c);
          const leftBL_L = this.getVEdgeIndex(r, c);

          // Get corner edges of right cell
          const rightTR_T = this.getHEdgeIndex(r, c + 1);
          const rightTR_R = this.getVEdgeIndex(r, c + 2);
          const rightBR_B = this.getHEdgeIndex(r + 1, c + 1);
          const rightBR_R = this.getVEdgeIndex(r, c + 2);

          // Case 2.1: BL of left cell is blocked (H(r+1,c) and V(r,c) are crosses)
          // AND TR of right cell is blocked (H(r,c+1) and V(r,c+2) are crosses)
          const blocked1 = isCornerBlocked(leftBL_B, leftBL_L) && isCornerBlocked(rightTR_T, rightTR_R);

          // Case 2.2: TL of left cell is blocked (H(r,c) and V(r,c) are crosses)
          // AND BR of right cell is blocked (H(r+1,c+1) and V(r,c+2) are crosses)
          const blocked2 = isCornerBlocked(leftTL_T, leftTL_L) && isCornerBlocked(rightBR_B, rightBR_R);

          if (blocked1 || blocked2) {
            // Line propagation:
            // If bottom edge bottomV is line (1), then top edge topV must be line (1)
            if (bottomV !== -1 && this.edgeStates[bottomV] === 1) {
              if (topV !== -1 && this.edgeStates[topV] === 0) {
                hints.push({
                  edgeIdx: topV,
                  state: 1,
                  reason: `横に並ぶ2つの1のマスにおいて、対角の角が×で塞がれており、下から線が入ってきたため、上側の辺は必ず線になります。`
                });
              }
            }
            // If top edge topV is line (1), then bottom edge bottomV must be line (1)
            if (topV !== -1 && this.edgeStates[topV] === 1) {
              if (bottomV !== -1 && this.edgeStates[bottomV] === 0) {
                hints.push({
                  edgeIdx: bottomV,
                  state: 1,
                  reason: `横に並ぶ2つの1のマスにおいて、対角の角が×で塞がれており、上から線が入ってきたため、下側の辺は必ず線になります。`
                });
              }
            }
          }
        }
      }
    }

    return hints;
  }

  // --- RULE 23: Adjacent 3 and 1 with Outside Cross ---
  checkAdjacent3And1WithOutsideCross() {
    const hints = [];

    // Helper to check if an edge is a cross (-1) or out of bounds (which functions as a cross)
    const isCrossOrOOB = (edgeIdx) => {
      if (edgeIdx === -1) return true; // Out of bounds is treated as cross
      return this.edgeStates[edgeIdx] === -1;
    };

    // 1. Vertically adjacent 3 and 1
    for (let r = 0; r < this.rows - 1; r++) {
      for (let c = 0; c < this.cols; c++) {
        const clueA = this.clues[r][c];
        const clueB = this.clues[r + 1][c];
        if ((clueA === 3 && clueB === 1) || (clueA === 1 && clueB === 3)) {
          const r3 = clueA === 3 ? r : r + 1;
          const r1 = clueA === 1 ? r : r + 1;
          // Boundary is H(r+1, c). Ends are P_left = (r+1, c) and P_right = (r+1, c+1)
          const rBoundary = r + 1;

          // Case 1.1: Left side has a cross. Left-pointing edge is H(rBoundary, c-1)
          const leftEdge = this.getHEdgeIndex(rBoundary, c - 1);
          if (isCrossOrOOB(leftEdge)) {
            // 3's left edge V(r3, c) should be line (1)
            const edge3L = this.getVEdgeIndex(r3, c);
            if (edge3L !== -1 && this.edgeStates[edge3L] === 0) {
              hints.push({
                edgeIdx: edge3L,
                state: 1,
                reason: `隣り合う3と1のマスにおいて、境界線の左側の辺が×（または盤面外）であるため、3の左側の辺は必ず線になります。`
              });
            }
            // 1's right edge V(r1, c+1) should be cross (-1)
            const edge1R = this.getVEdgeIndex(r1, c + 1);
            if (edge1R !== -1 && this.edgeStates[edge1R] === 0) {
              hints.push({
                edgeIdx: edge1R,
                state: -1,
                reason: `隣り合う3と1のマスにおいて、境界線の左側の辺が×（または盤面外）で3の左側の辺に線が入るため、1の右側の辺は必ず×になります。`
              });
            }
            // 1's opposite edge should be cross (-1)
            const oppEdgeIdx = r1 === r ? this.getHEdgeIndex(r1, c) : this.getHEdgeIndex(r1 + 1, c);
            if (oppEdgeIdx !== -1 && this.edgeStates[oppEdgeIdx] === 0) {
              const dirText = r1 === r ? '上側' : '下側';
              hints.push({
                edgeIdx: oppEdgeIdx,
                state: -1,
                reason: `隣り合う3と1のマスにおいて、境界線の左側の辺が×（または盤面外）で3の左側の辺に線が入るため、1の${dirText}の辺は必ず×になります。`
              });
            }
          }

          // Case 1.2: Right side has a cross. Right-pointing edge is H(rBoundary, c+1)
          const rightEdge = this.getHEdgeIndex(rBoundary, c + 1);
          if (isCrossOrOOB(rightEdge)) {
            // 3's right edge V(r3, c+1) should be line (1)
            const edge3R = this.getVEdgeIndex(r3, c + 1);
            if (edge3R !== -1 && this.edgeStates[edge3R] === 0) {
              hints.push({
                edgeIdx: edge3R,
                state: 1,
                reason: `隣り合う3と1のマスにおいて、境界線の右側の辺が×（または盤面外）であるため、3の右側の辺は必ず線になります。`
              });
            }
            // 1's left edge V(r1, c) should be cross (-1)
            const edge1L = this.getVEdgeIndex(r1, c);
            if (edge1L !== -1 && this.edgeStates[edge1L] === 0) {
              hints.push({
                edgeIdx: edge1L,
                state: -1,
                reason: `隣り合う3と1のマスにおいて、境界線の右側の辺が×（または盤面外）で3の右側の辺に線が入るため、1の左側の辺は必ず×になります。`
              });
            }
            // 1's opposite edge should be cross (-1)
            const oppEdgeIdx = r1 === r ? this.getHEdgeIndex(r1, c) : this.getHEdgeIndex(r1 + 1, c);
            if (oppEdgeIdx !== -1 && this.edgeStates[oppEdgeIdx] === 0) {
              const dirText = r1 === r ? '上側' : '下側';
              hints.push({
                edgeIdx: oppEdgeIdx,
                state: -1,
                reason: `隣り合う3と1のマスにおいて、境界線の右側の辺が×（または盤面外）で3の右側の辺に線が入るため、1の${dirText}の辺は必ず×になります。`
              });
            }
          }
        }
      }
    }

    // 2. Horizontally adjacent 3 and 1
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols - 1; c++) {
        const clueA = this.clues[r][c];
        const clueB = this.clues[r][c + 1];
        if ((clueA === 3 && clueB === 1) || (clueA === 1 && clueB === 3)) {
          const c3 = clueA === 3 ? c : c + 1;
          const c1 = clueA === 1 ? c : c + 1;
          // Boundary is V(r, c+1). Ends are P_top = (r, c+1) and P_bottom = (r+1, c+1)
          const cBoundary = c + 1;

          // Case 2.1: Top side has a cross. Upward edge is V(r-1, cBoundary)
          const topEdge = this.getVEdgeIndex(r - 1, cBoundary);
          if (isCrossOrOOB(topEdge)) {
            // 3's top edge H(r, c3) should be line (1)
            const edge3T = this.getHEdgeIndex(r, c3);
            if (edge3T !== -1 && this.edgeStates[edge3T] === 0) {
              hints.push({
                edgeIdx: edge3T,
                state: 1,
                reason: `隣り合う3と1のマスにおいて、境界線の上側の辺が×（または盤面外）であるため、3の上側の辺は必ず線になります。`
              });
            }
            // 1's bottom edge H(r+1, c1) should be cross (-1)
            const edge1B = this.getHEdgeIndex(r + 1, c1);
            if (edge1B !== -1 && this.edgeStates[edge1B] === 0) {
              hints.push({
                edgeIdx: edge1B,
                state: -1,
                reason: `隣り合う3と1のマスにおいて、境界線の上側の辺が×（または盤面外）で3の上側の辺に線が入るため、1の下側の辺は必ず×になります。`
              });
            }
            // 1's opposite edge should be cross (-1)
            const oppEdgeIdx = c1 === c ? this.getVEdgeIndex(r, c1) : this.getVEdgeIndex(r, c1 + 1);
            if (oppEdgeIdx !== -1 && this.edgeStates[oppEdgeIdx] === 0) {
              const dirText = c1 === c ? '左側' : '右側';
              hints.push({
                edgeIdx: oppEdgeIdx,
                state: -1,
                reason: `隣り合う3と1のマスにおいて、境界線の上側の辺が×（または盤面外）で3の上側の辺に線が入るため、1の${dirText}の辺は必ず×になります。`
              });
            }
          }

          // Case 2.2: Bottom side has a cross. Downward edge is V(r+1, cBoundary)
          const bottomEdge = this.getVEdgeIndex(r + 1, cBoundary);
          if (isCrossOrOOB(bottomEdge)) {
            // 3's bottom edge H(r+1, c3) should be line (1)
            const edge3B = this.getHEdgeIndex(r + 1, c3);
            if (edge3B !== -1 && this.edgeStates[edge3B] === 0) {
              hints.push({
                edgeIdx: edge3B,
                state: 1,
                reason: `隣り合う3と1のマスにおいて、境界線の下側の辺が×（または盤面外）であるため、3の下側の辺は必ず線になります。`
              });
            }
            // 1's top edge H(r, c1) should be cross (-1)
            const edge1T = this.getHEdgeIndex(r, c1);
            if (edge1T !== -1 && this.edgeStates[edge1T] === 0) {
              hints.push({
                edgeIdx: edge1T,
                state: -1,
                reason: `隣り合う3と1のマスにおいて、境界線の下側の辺が×（または盤面外）で3の下側の辺に線が入るため、1の上側の辺は必ず×になります。`
              });
            }
            // 1's opposite edge should be cross (-1)
            const oppEdgeIdx = c1 === c ? this.getVEdgeIndex(r, c1) : this.getVEdgeIndex(r, c1 + 1);
            if (oppEdgeIdx !== -1 && this.edgeStates[oppEdgeIdx] === 0) {
              const dirText = c1 === c ? '左側' : '右側';
              hints.push({
                edgeIdx: oppEdgeIdx,
                state: -1,
                reason: `隣り合う3と1のマスにおいて、境界線の下側の辺が×（または盤面外）で3の下側の辺に線が入るため、1の${dirText}の辺は必ず×になります。`
              });
            }
          }
        }
      }
    }

    return hints;
  }

  // --- RULE 24: Diagonal 3-2...2-3 with Any 2s in Between ---
  checkDiagonal323() {
    const hints = [];

    // Helper to scan in a diagonal direction from (r, c)
    const scanDiagonal = (startR, startC, dR, dC) => {
      let r = startR + dR;
      let c = startC + dC;
      let count2 = 0;

      while (r >= 0 && r < this.rows && c >= 0 && c < this.cols) {
        const clue = this.clues[r][c];
        if (clue === 2) {
          count2++;
          r += dR;
          c += dC;
        } else if (clue === 3) {
          // If we have at least one 2 in between
          if (count2 >= 1) {
            return { endR: r, endC: c };
          }
          return null;
        } else {
          return null;
        }
      }
      return null;
    };

    // 1. Scan Main Diagonal Direction (↘)
    for (let r = 0; r < this.rows - 2; r++) {
      for (let c = 0; c < this.cols - 2; c++) {
        if (this.clues[r][c] === 3) {
          const match = scanDiagonal(r, c, 1, 1);
          if (match) {
            const endR = match.endR;
            const endC = match.endC;

            // 1.1: Upper 3's outer corner (TL): H(r, c) and V(r, c)
            const topH = this.getHEdgeIndex(r, c);
            if (topH !== -1 && this.edgeStates[topH] === 0) {
              hints.push({
                edgeIdx: topH,
                state: 1,
                reason: `斜めに3と2が並んでいるため、端 of 3の外側の2辺（上辺と左辺）は必ず線になります。`
              });
            }
            const leftV = this.getVEdgeIndex(r, c);
            if (leftV !== -1 && this.edgeStates[leftV] === 0) {
              hints.push({
                edgeIdx: leftV,
                state: 1,
                reason: `斜めに3と2が並んでいるため、端 of 3の外側の2辺（上辺と左辺）は必ず線になります。`
              });
            }

            // 1.2: Lower 3's outer corner (BR): H(endR+1, endC) and V(endR, endC+1)
            const bottomH = this.getHEdgeIndex(endR + 1, endC);
            if (bottomH !== -1 && this.edgeStates[bottomH] === 0) {
              hints.push({
                edgeIdx: bottomH,
                state: 1,
                reason: `斜めに3と2が並んでいるため、端 of 3の外側の2辺（下辺と右辺）は必ず線になります。`
              });
            }
            const rightV = this.getVEdgeIndex(endR, endC + 1);
            if (rightV !== -1 && this.edgeStates[rightV] === 0) {
              hints.push({
                edgeIdx: rightV,
                state: 1,
                reason: `斜めに3と2が並んでいるため、端 of 3の外側の2辺（下辺と右辺）は必ず線になります。`
              });
            }
          }
        }
      }
    }

    // 2. Scan Sub Diagonal Direction (↙)
    for (let r = 0; r < this.rows - 2; r++) {
      for (let c = 2; c < this.cols; c++) {
        if (this.clues[r][c] === 3) {
          const match = scanDiagonal(r, c, 1, -1);
          if (match) {
            const endR = match.endR;
            const endC = match.endC;

            // 2.1: Upper 3's outer corner (TR): H(r, c) and V(r, c+1)
            const topH = this.getHEdgeIndex(r, c);
            if (topH !== -1 && this.edgeStates[topH] === 0) {
              hints.push({
                edgeIdx: topH,
                state: 1,
                reason: `斜めに3と2が並んでいるため、端 of 3の外側の2辺（上辺と右辺）は必ず線になります。`
              });
            }
            const rightV = this.getVEdgeIndex(r, c + 1);
            if (rightV !== -1 && this.edgeStates[rightV] === 0) {
              hints.push({
                edgeIdx: rightV,
                state: 1,
                reason: `斜めに3と2が並んでいるため、端 of 3の外側の2辺（上辺と右辺）は必ず線になります。`
              });
            }

            // 2.2: Lower 3's outer corner (BL): H(endR+1, endC) and V(endR, endC)
            const bottomH = this.getHEdgeIndex(endR + 1, endC);
            if (bottomH !== -1 && this.edgeStates[bottomH] === 0) {
              hints.push({
                edgeIdx: bottomH,
                state: 1,
                reason: `斜めに3と2が並んでいるため、端 of 3の外側の2辺（下辺と左辺）は必ず線になります。`
              });
            }
            const leftV = this.getVEdgeIndex(endR, endC);
            if (leftV !== -1 && this.edgeStates[leftV] === 0) {
              hints.push({
                edgeIdx: leftV,
                state: 1,
                reason: `斜めに3と2が並んでいるため、端 of 3の外側の2辺（下辺と左辺）は必ず線になります。`
              });
            }
          }
        }
      }
    }

    return hints;
  }

  // --- RULE 25: 3の角に隣接する2辺が線で、反対側に1がある場合の定石 (3 Corner Lines with Diagonal 1) ---
  check3CornerLinesWithDiagonal1() {
    const hints = [];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 3) continue;

        // We check all 4 diagonal neighbors of this '3' cell:
        const diagonals = [
          {
            // Case 1: 1 is at (r - 1, c - 1) (Top-Left)
            // 3's outer corner to check (BR): bottom and right edges
            r1: r - 1,
            c1: c - 1,
            checkEdges: [this.getHEdgeIndex(r + 1, c), this.getVEdgeIndex(r, c + 1)],
            // 1's outer corner to set to cross (TL): top and left edges of 1
            crossEdges: [this.getHEdgeIndex(r - 1, c - 1), this.getVEdgeIndex(r - 1, c - 1)]
          },
          {
            // Case 2: 1 is at (r - 1, c + 1) (Top-Right)
            // 3's outer corner to check (BL): bottom and left edges
            r1: r - 1,
            c1: c + 1,
            checkEdges: [this.getHEdgeIndex(r + 1, c), this.getVEdgeIndex(r, c)],
            // 1's outer corner to set to cross (TR): top and right edges of 1
            crossEdges: [this.getHEdgeIndex(r - 1, c + 1), this.getVEdgeIndex(r - 1, c + 2)]
          },
          {
            // Case 3: 1 is at (r + 1, c - 1) (Bottom-Left)
            // 3's outer corner to check (TR): top and right edges
            r1: r + 1,
            c1: c - 1,
            checkEdges: [this.getHEdgeIndex(r, c), this.getVEdgeIndex(r, c + 1)],
            // 1's outer corner to set to cross (BL): bottom and left edges of 1
            crossEdges: [this.getHEdgeIndex(r + 2, c - 1), this.getVEdgeIndex(r + 1, c - 1)]
          },
          {
            // Case 4: 1 is at (r + 1, c + 1) (Bottom-Right)
            // 3's outer corner to check (TL): top and left edges
            r1: r + 1,
            c1: c + 1,
            checkEdges: [this.getHEdgeIndex(r, c), this.getVEdgeIndex(r, c)],
            // 1's outer corner to set to cross (BR): bottom and right edges of 1
            crossEdges: [this.getHEdgeIndex(r + 2, c + 1), this.getVEdgeIndex(r + 1, c + 2)]
          }
        ];

        for (const diag of diagonals) {
          const { r1, c1, checkEdges, crossEdges } = diag;
          // Check bounds for the diagonal neighbor
          if (r1 < 0 || r1 >= this.rows || c1 < 0 || c1 >= this.cols) continue;
          if (this.clues[r1][c1] !== 1) continue;

          // Check if both outer edges of 3 are lines (state === 1)
          const [e3_1, e3_2] = checkEdges;
          if (e3_1 !== -1 && e3_2 !== -1 && this.edgeStates[e3_1] === 1 && this.edgeStates[e3_2] === 1) {
            // Deduce that both outer edges of 1 must be crosses (-1)
            for (const edgeIdx of crossEdges) {
              if (edgeIdx !== -1 && this.edgeStates[edgeIdx] === 0) {
                hints.push({
                  edgeIdx,
                  state: -1,
                  reason: `3の角に隣接する2辺が線で、反対側に1があるため、1の向こう側の辺は×になります。`
                });
              }
            }
          }
        }
      }
    }

    return hints;
  }

  // --- RULE 26: 2の角に隣接する辺が線と×で、反対側に3がある場合の定石 (2 Corner Line/Cross with Diagonal 3) ---
  check2CornerLineCrossWithDiagonal3() {
    const hints = [];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 2) continue;

        const diagonals = [
          {
            // Case 1: 3 is at (r - 1, c - 1) (Top-Left)
            // 2's corner to check (TL): top and left edges
            r3: r - 1,
            c3: c - 1,
            checkEdges: [this.getHEdgeIndex(r, c), this.getVEdgeIndex(r, c)],
            // 3's outer corner to set to line (TL): top and left edges of 3
            lineEdges: [this.getHEdgeIndex(r - 1, c - 1), this.getVEdgeIndex(r - 1, c - 1)]
          },
          {
            // Case 2: 3 is at (r - 1, c + 1) (Top-Right)
            // 2's corner to check (TR): top and right edges
            r3: r - 1,
            c3: c + 1,
            checkEdges: [this.getHEdgeIndex(r, c), this.getVEdgeIndex(r, c + 1)],
            // 3's outer corner to set to line (TR): top and right edges of 3
            lineEdges: [this.getHEdgeIndex(r - 1, c + 1), this.getVEdgeIndex(r - 1, c + 2)]
          },
          {
            // Case 3: 3 is at (r + 1, c - 1) (Bottom-Left)
            // 2's corner to check (BL): bottom and left edges
            r3: r + 1,
            c3: c - 1,
            checkEdges: [this.getHEdgeIndex(r + 1, c), this.getVEdgeIndex(r, c)],
            // 3's outer corner to set to line (BL): bottom and left edges of 3
            lineEdges: [this.getHEdgeIndex(r + 2, c - 1), this.getVEdgeIndex(r + 1, c - 1)]
          },
          {
            // Case 4: 3 is at (r + 1, c + 1) (Bottom-Right)
            // 2's corner to check (BR): bottom and right edges
            r3: r + 1,
            c3: c + 1,
            checkEdges: [this.getHEdgeIndex(r + 1, c), this.getVEdgeIndex(r, c + 1)],
            // 3's outer corner to set to line (BR): bottom and right edges of 3
            lineEdges: [this.getHEdgeIndex(r + 2, c + 1), this.getVEdgeIndex(r + 1, c + 2)]
          }
        ];

        for (const diag of diagonals) {
          const { r3, c3, checkEdges, lineEdges } = diag;
          if (r3 < 0 || r3 >= this.rows || c3 < 0 || c3 >= this.cols) continue;
          if (this.clues[r3][c3] !== 3) continue;

          // Check if one of 2's corner edges is a line (1) and the other is a cross (-1)
          const [e2_1, e2_2] = checkEdges;
          if (e2_1 !== -1 && e2_2 !== -1) {
            const s1 = this.edgeStates[e2_1];
            const s2 = this.edgeStates[e2_2];
            if ((s1 === 1 && s2 === -1) || (s1 === -1 && s2 === 1)) {
              // Deduce that both outer edges of 3 must be lines (1)
              for (const edgeIdx of lineEdges) {
                if (edgeIdx !== -1 && this.edgeStates[edgeIdx] === 0) {
                  hints.push({
                    edgeIdx,
                    state: 1,
                    reason: `2の角に隣接する2辺に線と×があるため、その反対側にある3の向こう側の辺は線になります。`
                  });
                }
              }
            }
          }
        }
      }
    }

    return hints;
  }

  // --- RULE 27: 1の角に隣接する2辺がxで、反対側の角の外側の片方がxの場合の定石 (1 Corner Crosses with Opposite Outside Cross) ---
  check1CornerCrossesOppositeOutsideCross() {
    const hints = [];
    const isCrossOrOOB = (edgeIdx) => {
      if (edgeIdx === -1) return true;
      return this.edgeStates[edgeIdx] === -1;
    };

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 1) continue;

        const corners = [
          {
            // Case 1: TL corner is cross -> BR opposite outside edges
            inside: [this.getHEdgeIndex(r, c), this.getVEdgeIndex(r, c)],
            outside: [this.getVEdgeIndex(r + 1, c + 1), this.getHEdgeIndex(r + 1, c + 1)]
          },
          {
            // Case 2: TR corner is cross -> BL opposite outside edges
            inside: [this.getHEdgeIndex(r, c), this.getVEdgeIndex(r, c + 1)],
            outside: [this.getVEdgeIndex(r + 1, c), this.getHEdgeIndex(r + 1, c - 1)]
          },
          {
            // Case 3: BL corner is cross -> TR opposite outside edges
            inside: [this.getHEdgeIndex(r + 1, c), this.getVEdgeIndex(r, c)],
            outside: [this.getVEdgeIndex(r - 1, c + 1), this.getHEdgeIndex(r, c + 1)]
          },
          {
            // Case 4: BR corner is cross -> TL opposite outside edges
            inside: [this.getHEdgeIndex(r + 1, c), this.getVEdgeIndex(r, c + 1)],
            outside: [this.getVEdgeIndex(r - 1, c), this.getHEdgeIndex(r, c - 1)]
          }
        ];

        for (const corner of corners) {
          const [in1, in2] = corner.inside;
          if (in1 !== -1 && in2 !== -1 && this.edgeStates[in1] === -1 && this.edgeStates[in2] === -1) {
            const [out1, out2] = corner.outside;
            
            if (isCrossOrOOB(out1)) {
              if (out2 !== -1 && this.edgeStates[out2] === 0) {
                hints.push({
                  edgeIdx: out2,
                  state: 1,
                  reason: `1のマスの角の2辺が×で、反対側の角の外側の片方も×（または盤面外）であるため、もう片方の辺は線になります。`
                });
              }
            }
            if (isCrossOrOOB(out2)) {
              if (out1 !== -1 && this.edgeStates[out1] === 0) {
                hints.push({
                  edgeIdx: out1,
                  state: 1,
                  reason: `1のマスの角の2辺が×で、反対側の角の外側の片方も×（または盤面外）であるため、もう片方の辺は線になります。`
                });
              }
            }
          }
        }
      }
    }

    return hints;
  }

  // --- RULE 28: 2の角に外側から線と×が入る場合の伝播定石 (2 Corner Outside Propagation) ---
  check2CornerOutsidePropagation() {
    const hints = [];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 2) continue;

        const corners = [
          {
            // Case 1: TL corner -> BR opposite outside
            outside: [this.getVEdgeIndex(r - 1, c), this.getHEdgeIndex(r, c - 1)],
            oppositeOutside: [this.getVEdgeIndex(r + 1, c + 1), this.getHEdgeIndex(r + 1, c + 1)]
          },
          {
            // Case 2: TR corner -> BL opposite outside
            outside: [this.getVEdgeIndex(r - 1, c + 1), this.getHEdgeIndex(r, c + 1)],
            oppositeOutside: [this.getVEdgeIndex(r + 1, c), this.getHEdgeIndex(r + 1, c - 1)]
          },
          {
            // Case 3: BL corner -> TR opposite outside
            outside: [this.getVEdgeIndex(r + 1, c), this.getHEdgeIndex(r + 1, c - 1)],
            oppositeOutside: [this.getVEdgeIndex(r - 1, c + 1), this.getHEdgeIndex(r, c + 1)]
          },
          {
            // Case 4: BR corner -> TL opposite outside
            outside: [this.getVEdgeIndex(r + 1, c + 1), this.getHEdgeIndex(r + 1, c + 1)],
            oppositeOutside: [this.getVEdgeIndex(r - 1, c), this.getHEdgeIndex(r, c - 1)]
          }
        ];

        for (const corner of corners) {
          const [out1, out2] = corner.outside;
          const sOut1 = out1 !== -1 ? this.edgeStates[out1] : -1;
          const sOut2 = out2 !== -1 ? this.edgeStates[out2] : -1;

          // Condition: one of outside edges of this corner is line (1) and the other is cross (-1 or OOB)
          const hasOneLineOneCross = (sOut1 === 1 && sOut2 === -1) || (sOut1 === -1 && sOut2 === 1);
          if (hasOneLineOneCross) {
            const [opp1, opp2] = corner.oppositeOutside;
            const sOpp1 = opp1 !== -1 ? this.edgeStates[opp1] : -1;
            const sOpp2 = opp2 !== -1 ? this.edgeStates[opp2] : -1;

            // opp1 deduction:
            if (opp1 !== -1 && this.edgeStates[opp1] === 0) {
              if (sOpp2 === 1) {
                hints.push({
                  edgeIdx: opp1,
                  state: -1,
                  reason: `2のマスの片方の角に外側から線と×が入るため、反対側の角からも線と×が出る性質により、ここは×になります。`
                });
              } else if (sOpp2 === -1) {
                hints.push({
                  edgeIdx: opp1,
                  state: 1,
                  reason: `2のマスの片方の角に外側から線と×が入るため、反対側の角からも線と×が出る性質により、ここは線になります。`
                });
              }
            }

            // opp2 deduction:
            if (opp2 !== -1 && this.edgeStates[opp2] === 0) {
              if (sOpp1 === 1) {
                hints.push({
                  edgeIdx: opp2,
                  state: -1,
                  reason: `2のマスの片方の角に外側から線と×が入るため、反対側の角からも線と×が出る性質により、ここは×になります。`
                });
              } else if (sOpp1 === -1) {
                hints.push({
                  edgeIdx: opp2,
                  state: 1,
                  reason: `2のマスの片方の角に外側から線と×が入るため、反対側の角からも線と×が出る性質により、ここは線になります。`
                });
              }
            }
          }
        }
      }
    }

    return hints;
  }

  // --- RULE 29: 斜めに対角に隣り合う1と1の外側2×の伝播定石 (Diagonal 1s Outside Crosses) ---
  checkDiagonal1sOutsideCrosses() {
    const hints = [];

    for (let r = 0; r < this.rows - 1; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 1) continue;

        // We check two diagonal directions: Bottom-Right and Bottom-Left
        
        // Case 1: Bottom-Right neighbor (r+1, c+1) is also 1
        if (c + 1 < this.cols && this.clues[r + 1][c + 1] === 1) {
          const A_outer = [this.getHEdgeIndex(r, c), this.getVEdgeIndex(r, c)]; // TL of A
          const B_outer = [this.getHEdgeIndex(r + 2, c + 1), this.getVEdgeIndex(r + 1, c + 2)]; // BR of B
          
          const A_has_crosses = A_outer[0] !== -1 && A_outer[1] !== -1 &&
                                this.edgeStates[A_outer[0]] === -1 && this.edgeStates[A_outer[1]] === -1;
          if (A_has_crosses) {
            for (const edgeIdx of B_outer) {
              if (edgeIdx !== -1 && this.edgeStates[edgeIdx] === 0) {
                hints.push({
                  edgeIdx,
                  state: -1,
                  reason: `斜めに並んだ1と1において、片方の外側2辺が×であるため、もう片方の外側2辺も×になります。`
                });
              }
            }
          }

          const B_has_crosses = B_outer[0] !== -1 && B_outer[1] !== -1 &&
                                this.edgeStates[B_outer[0]] === -1 && this.edgeStates[B_outer[1]] === -1;
          if (B_has_crosses) {
            for (const edgeIdx of A_outer) {
              if (edgeIdx !== -1 && this.edgeStates[edgeIdx] === 0) {
                hints.push({
                  edgeIdx,
                  state: -1,
                  reason: `斜めに並んだ1と1において、片方の外側2辺が×であるため、もう片方の外側2辺も×になります。`
                });
              }
            }
          }
        }

        // Case 2: Bottom-Left neighbor (r+1, c-1) is also 1
        if (c - 1 >= 0 && this.clues[r + 1][c - 1] === 1) {
          const A_outer = [this.getHEdgeIndex(r, c), this.getVEdgeIndex(r, c + 1)]; // TR of A
          const B_outer = [this.getHEdgeIndex(r + 2, c - 1), this.getVEdgeIndex(r + 1, c - 1)]; // BL of B

          const A_has_crosses = A_outer[0] !== -1 && A_outer[1] !== -1 &&
                                this.edgeStates[A_outer[0]] === -1 && this.edgeStates[A_outer[1]] === -1;
          if (A_has_crosses) {
            for (const edgeIdx of B_outer) {
              if (edgeIdx !== -1 && this.edgeStates[edgeIdx] === 0) {
                hints.push({
                  edgeIdx,
                  state: -1,
                  reason: `斜めに並んだ1と1において、片方の外側2辺が×であるため、もう片方の外側2辺も×になります。`
                });
              }
            }
          }

          const B_has_crosses = B_outer[0] !== -1 && B_outer[1] !== -1 &&
                                this.edgeStates[B_outer[0]] === -1 && this.edgeStates[B_outer[1]] === -1;
          if (B_has_crosses) {
            for (const edgeIdx of A_outer) {
              if (edgeIdx !== -1 && this.edgeStates[edgeIdx] === 0) {
                hints.push({
                  edgeIdx,
                  state: -1,
                  reason: `斜めに並んだ1と1において、片方の外側2辺が×であるため、もう片方の外側2辺も×になります。`
                });
              }
            }
          }
        }
      }
    }

    return hints;
  }



  // --- RULE 16: 1の角の外側にxが2つある場合の定石 (1 Corner Outside Crosses) ---
  check1CornerOutsideCrosses() {
    const hints = [];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 1) continue;

        const cellHtop = this.getHEdgeIndex(r, c);
        const cellHbottom = this.getHEdgeIndex(r + 1, c);
        const cellVleft = this.getVEdgeIndex(r, c);
        const cellVright = this.getVEdgeIndex(r, c + 1);

        const corners = [
          {
            name: '左上',
            outside: [
              this.getVEdgeIndex(r - 1, c),
              this.getHEdgeIndex(r, c - 1)
            ],
            inside: [cellHtop, cellVleft]
          },
          {
            name: '右上',
            outside: [
              this.getVEdgeIndex(r - 1, c + 1),
              this.getHEdgeIndex(r, c + 1)
            ],
            inside: [cellHtop, cellVright]
          },
          {
            name: '左下',
            outside: [
              this.getVEdgeIndex(r + 1, c),
              this.getHEdgeIndex(r + 1, c - 1)
            ],
            inside: [cellHbottom, cellVleft]
          },
          {
            name: '右下',
            outside: [
              this.getVEdgeIndex(r + 1, c + 1),
              this.getHEdgeIndex(r + 1, c + 1)
            ],
            inside: [cellHbottom, cellVright]
          }
        ];

        for (const corner of corners) {
          const isCross = (edgeIdx) => {
            if (edgeIdx === -1) return true; // Out of bounds is treated as cross
            return this.edgeStates[edgeIdx] === -1;
          };

          if (isCross(corner.outside[0]) && isCross(corner.outside[1])) {
            for (const inEdge of corner.inside) {
              if (this.edgeStates[inEdge] === 0) {
                hints.push({
                  edgeIdx: inEdge,
                  state: -1,
                  reason: `1のマスの${corner.name}の角から外へ伸びる2つの辺が×（または盤面外）のため、その角を構成するマスの2辺は必ず×になります。`
                });
              }
            }
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 17: 1の角の外側がx2つで、対角に線が入ってきた場合の定石 (1 Corner Outside Crosses Opposite Entry) ---
  check1CornerOutsideCrossesOppositeEntry() {
    const hints = [];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 1) continue;

        const corners = [
          {
            id: 0, // TL
            name: '左上',
            outside: [
              this.getVEdgeIndex(r - 1, c), // Up
              this.getHEdgeIndex(r, c - 1)  // Left
            ],
            oppositeId: 3, // BR
            oppositeName: '右下'
          },
          {
            id: 1, // TR
            name: '右上',
            outside: [
              this.getVEdgeIndex(r - 1, c + 1), // Up
              this.getHEdgeIndex(r, c + 1)      // Right
            ],
            oppositeId: 2, // BL
            oppositeName: '左下'
          },
          {
            id: 2, // BL
            name: '左下',
            outside: [
              this.getVEdgeIndex(r + 1, c),     // Down
              this.getHEdgeIndex(r + 1, c - 1)  // Left
            ],
            oppositeId: 1, // TR
            oppositeName: '右上'
          },
          {
            id: 3, // BR
            name: '右下',
            outside: [
              this.getVEdgeIndex(r + 1, c + 1), // Down
              this.getHEdgeIndex(r + 1, c + 1)  // Right
            ],
            oppositeId: 0, // TL
            oppositeName: '左上'
          }
        ];

        const isCross = (edgeIdx) => {
          if (edgeIdx === -1) return true; // Out of bounds is treated as cross
          return this.edgeStates[edgeIdx] === -1;
        };

        for (let i = 0; i < 4; i++) {
          const base = corners[i];
          // If base corner has 2 outside crosses
          if (isCross(base.outside[0]) && isCross(base.outside[1])) {
            const opp = corners[base.oppositeId];
            const oppOut0 = opp.outside[0];
            const oppOut1 = opp.outside[1];

            const s0 = oppOut0 === -1 ? -1 : this.edgeStates[oppOut0];
            const s1 = oppOut1 === -1 ? -1 : this.edgeStates[oppOut1];

            // If one outside edge of the opposite corner is a line (1)
            // and the other is undecided (0)
            if (s0 === 1 && s1 === 0 && oppOut1 !== -1) {
              hints.push({
                edgeIdx: oppOut1,
                state: -1,
                reason: `1のマスの${base.name}の角の外側が×で、対角の${opp.name}の角に外から線が入ってきたため、もう一方の辺は×になります。`
              });
            } else if (s1 === 1 && s0 === 0 && oppOut0 !== -1) {
              hints.push({
                edgeIdx: oppOut0,
                state: -1,
                reason: `1のマスの${base.name}の角の外側が×で、対角の${opp.name}の角に外から線が入ってきたため、もう一方の辺は×になります。`
              });
            }
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 18: 2の周囲に線とxが隣接し、対角の外側片方がxの場合の定石 (2 Opposite Line From Line Cross) ---
  check2OppositeLineFromLineCross() {
    const hints = [];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 2) continue;

        const cellHtop = this.getHEdgeIndex(r, c);
        const cellHbottom = this.getHEdgeIndex(r + 1, c);
        const cellVleft = this.getVEdgeIndex(r, c);
        const cellVright = this.getVEdgeIndex(r, c + 1);

        const corners = [
          {
            id: 0, // TL
            name: '左上',
            inside: [cellHtop, cellVleft],
            oppositeId: 3, // BR
            oppositeName: '右下'
          },
          {
            id: 1, // TR
            name: '右上',
            inside: [cellHtop, cellVright],
            oppositeId: 2, // BL
            oppositeName: '左下'
          },
          {
            id: 2, // BL
            name: '左下',
            inside: [cellHbottom, cellVleft],
            oppositeId: 1, // TR
            oppositeName: '右上'
          },
          {
            id: 3, // BR
            name: '右下',
            inside: [cellHbottom, cellVright],
            oppositeId: 0, // TL
            oppositeName: '左上'
          }
        ];

        const oppOutside = [
          [this.getVEdgeIndex(r - 1, c), this.getHEdgeIndex(r, c - 1)],       // opp TL
          [this.getVEdgeIndex(r - 1, c + 1), this.getHEdgeIndex(r, c + 1)],   // opp TR
          [this.getVEdgeIndex(r + 1, c), this.getHEdgeIndex(r + 1, c - 1)],   // opp BL
          [this.getVEdgeIndex(r + 1, c + 1), this.getHEdgeIndex(r + 1, c + 1)] // opp BR
        ];

        for (let i = 0; i < 4; i++) {
          const base = corners[i];
          const s0 = this.edgeStates[base.inside[0]];
          const s1 = this.edgeStates[base.inside[1]];

          // If inside edges adjacent to this corner have 1 line and 1 cross
          if ((s0 === 1 && s1 === -1) || (s0 === -1 && s1 === 1)) {
            const opp = corners[base.oppositeId];
            const oppOut0 = oppOutside[base.oppositeId][0];
            const oppOut1 = oppOutside[base.oppositeId][1];

            const o0 = oppOut0 === -1 ? -1 : this.edgeStates[oppOut0];
            const o1 = oppOut1 === -1 ? -1 : this.edgeStates[oppOut1];

            // If one outside edge of opposite corner is cross (-1) and the other is undecided (0)
            if (o0 === -1 && o1 === 0 && oppOut1 !== -1) {
              hints.push({
                edgeIdx: oppOut1,
                state: 1,
                reason: `2のマスの${base.name}の隣り合う辺に線と×があるため対角の${opp.name}の角から線が出ることになり、外側の片方が×のため、もう一方に線が入ります。`
              });
            } else if (o1 === -1 && o0 === 0 && oppOut0 !== -1) {
              hints.push({
                edgeIdx: oppOut0,
                state: 1,
                reason: `2のマスの${base.name}の隣り合う辺に線と×があるため対角の${opp.name}の角から線が出ることになり、外側の片方が×のため、もう一方に線が入ります。`
              });
            }
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 19: 2の角に線とxが隣接し、対角の外側に線が入ってきた場合の定石 (2 Opposite Cross From Line Cross) ---
  check2OppositeCrossFromLineCross() {
    const hints = [];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 2) continue;

        const cellHtop = this.getHEdgeIndex(r, c);
        const cellHbottom = this.getHEdgeIndex(r + 1, c);
        const cellVleft = this.getVEdgeIndex(r, c);
        const cellVright = this.getVEdgeIndex(r, c + 1);

        const corners = [
          {
            id: 0, // TL
            name: '左上',
            inside: [cellHtop, cellVleft],
            oppositeId: 3, // BR
            oppositeName: '右下'
          },
          {
            id: 1, // TR
            name: '右上',
            inside: [cellHtop, cellVright],
            oppositeId: 2, // BL
            oppositeName: '左下'
          },
          {
            id: 2, // BL
            name: '左下',
            inside: [cellHbottom, cellVleft],
            oppositeId: 1, // TR
            oppositeName: '右上'
          },
          {
            id: 3, // BR
            name: '右下',
            inside: [cellHbottom, cellVright],
            oppositeId: 0, // TL
            oppositeName: '左上'
          }
        ];

        const oppOutside = [
          [this.getVEdgeIndex(r - 1, c), this.getHEdgeIndex(r, c - 1)],       // opp TL
          [this.getVEdgeIndex(r - 1, c + 1), this.getHEdgeIndex(r, c + 1)],   // opp TR
          [this.getVEdgeIndex(r + 1, c), this.getHEdgeIndex(r + 1, c - 1)],   // opp BL
          [this.getVEdgeIndex(r + 1, c + 1), this.getHEdgeIndex(r + 1, c + 1)] // opp BR
        ];

        for (let i = 0; i < 4; i++) {
          const base = corners[i];
          const s0 = this.edgeStates[base.inside[0]];
          const s1 = this.edgeStates[base.inside[1]];

          // If inside edges adjacent to this corner have 1 line and 1 cross
          if ((s0 === 1 && s1 === -1) || (s0 === -1 && s1 === 1)) {
            const opp = corners[base.oppositeId];
            const oppOut0 = oppOutside[base.oppositeId][0];
            const oppOut1 = oppOutside[base.oppositeId][1];

            const o0 = oppOut0 === -1 ? -1 : this.edgeStates[oppOut0];
            const o1 = oppOut1 === -1 ? -1 : this.edgeStates[oppOut1];

            // If one outside edge of opposite corner is line (1) and the other is undecided (0)
            if (o0 === 1 && o1 === 0 && oppOut1 !== -1) {
              hints.push({
                edgeIdx: oppOut1,
                state: -1,
                reason: `2のマスの${base.name}の隣り合う辺に線と×があり、対角の${opp.name}の角に外から線が入ってきたため、もう一方の辺は×になります。`
              });
            } else if (o1 === 1 && o0 === 0 && oppOut0 !== -1) {
              hints.push({
                edgeIdx: oppOut0,
                state: -1,
                reason: `2のマスの${base.name}の隣り合う辺に線と×があり、対角の${opp.name}の角に外から線が入ってきたため、もう一方の辺は×になります。`
              });
            }
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 20: 3 of Corner Two Lines Opposite Outside Cross (3 Opposite Line From Two Lines) ---
  check3OppositeLineFromTwoLines() {
    const hints = [];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 3) continue;

        const cellHtop = this.getHEdgeIndex(r, c);
        const cellHbottom = this.getHEdgeIndex(r + 1, c);
        const cellVleft = this.getVEdgeIndex(r, c);
        const cellVright = this.getVEdgeIndex(r, c + 1);

        const corners = [
          {
            id: 0, // TL
            name: '左上',
            inside: [cellHtop, cellVleft],
            oppositeId: 3, // BR
            oppositeName: '右下'
          },
          {
            id: 1, // TR
            name: '右上',
            inside: [cellHtop, cellVright],
            oppositeId: 2, // BL
            oppositeName: '左下'
          },
          {
            id: 2, // BL
            name: '左下',
            inside: [cellHbottom, cellVleft],
            oppositeId: 1, // TR
            oppositeName: '右上'
          },
          {
            id: 3, // BR
            name: '右下',
            inside: [cellHbottom, cellVright],
            oppositeId: 0, // TL
            oppositeName: '左上'
          }
        ];

        const oppOutside = [
          [this.getVEdgeIndex(r - 1, c), this.getHEdgeIndex(r, c - 1)],       // opp TL
          [this.getVEdgeIndex(r - 1, c + 1), this.getHEdgeIndex(r, c + 1)],   // opp TR
          [this.getVEdgeIndex(r + 1, c), this.getHEdgeIndex(r + 1, c - 1)],   // opp BL
          [this.getVEdgeIndex(r + 1, c + 1), this.getHEdgeIndex(r + 1, c + 1)] // opp BR
        ];

        for (let i = 0; i < 4; i++) {
          const base = corners[i];
          const s0 = this.edgeStates[base.inside[0]];
          const s1 = this.edgeStates[base.inside[1]];

          // If inside edges adjacent to base corner are both lines (1)
          if (s0 === 1 && s1 === 1) {
            const opp = corners[base.oppositeId];
            const oppOut0 = oppOutside[base.oppositeId][0];
            const oppOut1 = oppOutside[base.oppositeId][1];

            const o0 = oppOut0 === -1 ? -1 : this.edgeStates[oppOut0];
            const o1 = oppOut1 === -1 ? -1 : this.edgeStates[oppOut1];

            // If one outside edge of opposite corner is cross (-1) and the other is undecided (0)
            if (o0 === -1 && o1 === 0 && oppOut1 !== -1) {
              hints.push({
                edgeIdx: oppOut1,
                state: 1,
                reason: `3のマスの${base.name}の角に線が2本あるため対角の${opp.name}の角から線が1本出ることになり、外側の片方が×のため、もう一方に線が入ります。`
              });
            } else if (o1 === -1 && o0 === 0 && oppOut0 !== -1) {
              hints.push({
                edgeIdx: oppOut0,
                state: 1,
                reason: `3のマスの${base.name}の角に線が2本あるため対角の${opp.name}の角から線が1本出ることになり、外側の片方が×のため、もう一方に線が入ります。`
              });
            }
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 21: 3 of Corner Two Lines Opposite Outside Line (3 Opposite Cross From Two Lines) ---
  check3OppositeCrossFromTwoLines() {
    const hints = [];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 3) continue;

        const cellHtop = this.getHEdgeIndex(r, c);
        const cellHbottom = this.getHEdgeIndex(r + 1, c);
        const cellVleft = this.getVEdgeIndex(r, c);
        const cellVright = this.getVEdgeIndex(r, c + 1);

        const corners = [
          {
            id: 0, // TL
            name: '左上',
            inside: [cellHtop, cellVleft],
            oppositeId: 3, // BR
            oppositeName: '右下'
          },
          {
            id: 1, // TR
            name: '右上',
            inside: [cellHtop, cellVright],
            oppositeId: 2, // BL
            oppositeName: '左下'
          },
          {
            id: 2, // BL
            name: '左下',
            inside: [cellHbottom, cellVleft],
            oppositeId: 1, // TR
            oppositeName: '右上'
          },
          {
            id: 3, // BR
            name: '右下',
            inside: [cellHbottom, cellVright],
            oppositeId: 0, // TL
            oppositeName: '左上'
          }
        ];

        const oppOutside = [
          [this.getVEdgeIndex(r - 1, c), this.getHEdgeIndex(r, c - 1)],       // opp TL
          [this.getVEdgeIndex(r - 1, c + 1), this.getHEdgeIndex(r, c + 1)],   // opp TR
          [this.getVEdgeIndex(r + 1, c), this.getHEdgeIndex(r + 1, c - 1)],   // opp BL
          [this.getVEdgeIndex(r + 1, c + 1), this.getHEdgeIndex(r + 1, c + 1)] // opp BR
        ];

        for (let i = 0; i < 4; i++) {
          const base = corners[i];
          const s0 = this.edgeStates[base.inside[0]];
          const s1 = this.edgeStates[base.inside[1]];

          // If inside edges adjacent to base corner are both lines (1)
          if (s0 === 1 && s1 === 1) {
            const opp = corners[base.oppositeId];
            const oppOut0 = oppOutside[base.oppositeId][0];
            const oppOut1 = oppOutside[base.oppositeId][1];

            const o0 = oppOut0 === -1 ? -1 : this.edgeStates[oppOut0];
            const o1 = oppOut1 === -1 ? -1 : this.edgeStates[oppOut1];

            // If one outside edge of opposite corner is line (1) and the other is undecided (0)
            if (o0 === 1 && o1 === 0 && oppOut1 !== -1) {
              hints.push({
                edgeIdx: oppOut1,
                state: -1,
                reason: `3のマスの${base.name}の角に線が2本あるため対角の${opp.name}の角から線が1本出ることになり、外側の片方に線が入ってきたため、もう一方の辺は×になります。`
              });
            } else if (o1 === 1 && o0 === 0 && oppOut0 !== -1) {
              hints.push({
                edgeIdx: oppOut0,
                state: -1,
                reason: `3のマスの${base.name}の角に線が2本あるため対角の${opp.name}の角から線が1本出ることになり、外側の片方に線が入ってきたため、もう一方の辺は×になります。`
              });
            }
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 10: 3の角に外から線が入ってきた場合の定石 (3 Corner Line Entry) ---
  check3CornerLineEntry() {
    const hints = [];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 3) continue;

        const cellHtop = this.getHEdgeIndex(r, c);
        const cellHbottom = this.getHEdgeIndex(r + 1, c);
        const cellVleft = this.getVEdgeIndex(r, c);
        const cellVright = this.getVEdgeIndex(r, c + 1);

        // 4 corners of the 3 cell, and their entering outside edges
        const corners = [
          {
            name: '左上',
            outside: [
              { edge: this.getVEdgeIndex(r - 1, c), otherOutside: this.getHEdgeIndex(r, c - 1) }, // Up
              { edge: this.getHEdgeIndex(r, c - 1), otherOutside: this.getVEdgeIndex(r - 1, c) }  // Left
            ],
            opposite: [cellHbottom, cellVright]
          },
          {
            name: '右上',
            outside: [
              { edge: this.getVEdgeIndex(r - 1, c + 1), otherOutside: this.getHEdgeIndex(r, c + 1) }, // Up
              { edge: this.getHEdgeIndex(r, c + 1), otherOutside: this.getVEdgeIndex(r - 1, c + 1) }  // Right
            ],
            opposite: [cellHbottom, cellVleft]
          },
          {
            name: '左下',
            outside: [
              { edge: this.getVEdgeIndex(r + 1, c), otherOutside: this.getHEdgeIndex(r + 1, c - 1) }, // Down
              { edge: this.getHEdgeIndex(r + 1, c - 1), otherOutside: this.getVEdgeIndex(r + 1, c) }  // Left
            ],
            opposite: [cellHtop, cellVright]
          },
          {
            name: '右下',
            outside: [
              { edge: this.getVEdgeIndex(r + 1, c + 1), otherOutside: this.getHEdgeIndex(r + 1, c + 1) }, // Down
              { edge: this.getHEdgeIndex(r + 1, c + 1), otherOutside: this.getVEdgeIndex(r + 1, c + 1) }  // Right
            ],
            opposite: [cellHtop, cellVleft]
          }
        ];

        for (const corner of corners) {
          for (const item of corner.outside) {
            if (item.edge !== -1 && this.edgeStates[item.edge] === 1) {
              // Line enters this corner of the 3 cell from the outside!
              
              // 1. Opposite two edges of the 3 cell must be lines
              for (const oppEdge of corner.opposite) {
                if (this.edgeStates[oppEdge] === 0) {
                  hints.push({
                    edgeIdx: oppEdge,
                    state: 1,
                    reason: `3のマスの${corner.name}の角に外から線が入っているため、その対面にある2辺は必ず線になります。`
                  });
                }
              }

              // 2. The other outside edge must be a cross (x)
              if (item.otherOutside !== -1 && this.edgeStates[item.otherOutside] === 0) {
                hints.push({
                  edgeIdx: item.otherOutside,
                  state: -1,
                  reason: `3のマスの${corner.name}の角に外から線が入っているため、角から外へ逃げるもう一方の辺は×になります。`
                });
              }
            }
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 11: 1の角に線が入り、もう一方が×の場合の定石 (1 Corner Line Entry) ---
  check1CornerLineEntry() {
    const hints = [];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 1) continue;

        const cellHtop = this.getHEdgeIndex(r, c);
        const cellHbottom = this.getHEdgeIndex(r + 1, c);
        const cellVleft = this.getVEdgeIndex(r, c);
        const cellVright = this.getVEdgeIndex(r, c + 1);

        const corners = [
          {
            name: '左上',
            out1: this.getVEdgeIndex(r - 1, c),
            out2: this.getHEdgeIndex(r, c - 1),
            opposite: [cellHbottom, cellVright]
          },
          {
            name: '右上',
            out1: this.getVEdgeIndex(r - 1, c + 1),
            out2: this.getHEdgeIndex(r, c + 1),
            opposite: [cellHbottom, cellVleft]
          },
          {
            name: '左下',
            out1: this.getVEdgeIndex(r + 1, c),
            out2: this.getHEdgeIndex(r + 1, c - 1),
            opposite: [cellHtop, cellVright]
          },
          {
            name: '右下',
            out1: this.getVEdgeIndex(r + 1, c + 1),
            out2: this.getHEdgeIndex(r + 1, c + 1),
            opposite: [cellHtop, cellVleft]
          }
        ];

        for (const corner of corners) {
          const getState = (edgeIdx) => {
            if (edgeIdx === -1) return -1; // Out of bounds is treated as cross (-1)
            return this.edgeStates[edgeIdx];
          };

          const s1 = getState(corner.out1);
          const s2 = getState(corner.out2);

          // If one outside edge is a line (1) and the other is a cross (-1)
          if ((s1 === 1 && s2 === -1) || (s2 === 1 && s1 === -1)) {
            for (const oppEdge of corner.opposite) {
              if (this.edgeStates[oppEdge] === 0) {
                hints.push({
                  edgeIdx: oppEdge,
                  state: -1,
                  reason: `1のマスの${corner.name}の角に線が入ってきて、もう一方が×（または盤面外）のため、その対面にある2辺は必ず×になります。`
                });
              }
            }
          }
        }
      }
    }
    return hints;
  }

  // --- RULE 12: 隣接する3の横に2がある場合の定石 (Adjacent 3s with 2) ---
  checkAdjacent3sWith2() {
    const hints = [];

    // --- CASE 1: Horizontally adjacent 3s at (r, c) and (r, c + 1) ---
    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols - 1; c++) {
        if (this.clues[r][c] === 3 && this.clues[r][c + 1] === 3) {
          
          // Subcase 1.1: 2 is below left 3 at (r + 1, c)
          if (r + 1 < this.rows && this.clues[r + 1][c] === 2) {
            const bottomOf2 = this.getHEdgeIndex(r + 2, c);
            if (bottomOf2 !== -1 && this.edgeStates[bottomOf2] === 0) {
              hints.push({
                edgeIdx: bottomOf2,
                state: 1,
                reason: `隣接する3のマスの隣に2のマスがあるため、2のマスの対面の辺は必ず線になります。`
              });
            }
            const leftExt = this.getHEdgeIndex(r + 1, c - 1);
            if (leftExt !== -1 && this.edgeStates[leftExt] === 0) {
              hints.push({
                edgeIdx: leftExt,
                state: -1,
                reason: `隣接する3のマスの隣に2のマスがあるため、3のマスの角から外へ逃げる辺は必ず×になります。`
              });
            }
          }

          // Subcase 1.2: 2 is below right 3 at (r + 1, c + 1)
          if (r + 1 < this.rows && this.clues[r + 1][c + 1] === 2) {
            const bottomOf2 = this.getHEdgeIndex(r + 2, c + 1);
            if (bottomOf2 !== -1 && this.edgeStates[bottomOf2] === 0) {
              hints.push({
                edgeIdx: bottomOf2,
                state: 1,
                reason: `隣接する3のマスの隣に2のマスがあるため、2のマスの対面の辺は必ず線になります。`
              });
            }
            const rightExt = this.getHEdgeIndex(r + 1, c + 2);
            if (rightExt !== -1 && this.edgeStates[rightExt] === 0) {
              hints.push({
                edgeIdx: rightExt,
                state: -1,
                reason: `隣接する3のマスの隣に2のマスがあるため、3のマスの角から外へ逃げる辺は必ず×になります。`
              });
            }
          }

          // Subcase 1.3: 2 is above left 3 at (r - 1, c)
          if (r - 1 >= 0 && this.clues[r - 1][c] === 2) {
            const topOf2 = this.getHEdgeIndex(r - 1, c);
            if (topOf2 !== -1 && this.edgeStates[topOf2] === 0) {
              hints.push({
                edgeIdx: topOf2,
                state: 1,
                reason: `隣接する3のマスの隣に2のマスがあるため、2のマスの対面の辺は必ず線になります。`
              });
            }
            const leftExt = this.getHEdgeIndex(r, c - 1);
            if (leftExt !== -1 && this.edgeStates[leftExt] === 0) {
              hints.push({
                edgeIdx: leftExt,
                state: -1,
                reason: `隣接する3のマスの隣に2のマスがあるため、3のマスの角から外へ逃げる辺は必ず×になります。`
              });
            }
          }

          // Subcase 1.4: 2 is above right 3 at (r - 1, c + 1)
          if (r - 1 >= 0 && this.clues[r - 1][c + 1] === 2) {
            const topOf2 = this.getHEdgeIndex(r - 1, c + 1);
            if (topOf2 !== -1 && this.edgeStates[topOf2] === 0) {
              hints.push({
                edgeIdx: topOf2,
                state: 1,
                reason: `隣接する3のマスの隣に2のマスがあるため、2のマスの対面の辺は必ず線になります。`
              });
            }
            const rightExt = this.getHEdgeIndex(r, c + 2);
            if (rightExt !== -1 && this.edgeStates[rightExt] === 0) {
              hints.push({
                edgeIdx: rightExt,
                state: -1,
                reason: `隣接する3のマスの隣に2のマスがあるため、3のマスの角から外へ逃げる辺は必ず×になります。`
              });
            }
          }

        }
      }
    }

    // --- CASE 2: Vertically adjacent 3s at (r, c) and (r + 1, c) ---
    for (let r = 0; r < this.rows - 1; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] === 3 && this.clues[r + 1][c] === 3) {

          // Subcase 2.1: 2 is right of top 3 at (r, c + 1)
          if (c + 1 < this.cols && this.clues[r][c + 1] === 2) {
            const rightOf2 = this.getVEdgeIndex(r, c + 2);
            if (rightOf2 !== -1 && this.edgeStates[rightOf2] === 0) {
              hints.push({
                edgeIdx: rightOf2,
                state: 1,
                reason: `隣接する3のマスの隣に2のマスがあるため、2のマスの対面の辺は必ず線になります。`
              });
            }
            const topExt = this.getVEdgeIndex(r - 1, c + 1);
            if (topExt !== -1 && this.edgeStates[topExt] === 0) {
              hints.push({
                edgeIdx: topExt,
                state: -1,
                reason: `隣接する3のマスの隣に2のマスがあるため、3のマスの角から外へ逃げる辺は必ず×になります。`
              });
            }
          }

          // Subcase 2.2: 2 is right of bottom 3 at (r + 1, c + 1)
          if (c + 1 < this.cols && this.clues[r + 1][c + 1] === 2) {
            const rightOf2 = this.getVEdgeIndex(r + 1, c + 2);
            if (rightOf2 !== -1 && this.edgeStates[rightOf2] === 0) {
              hints.push({
                edgeIdx: rightOf2,
                state: 1,
                reason: `隣接する3のマスの隣に2のマスがあるため、2のマスの対面の辺は必ず線になります。`
              });
            }
            const bottomExt = this.getVEdgeIndex(r + 2, c + 1);
            if (bottomExt !== -1 && this.edgeStates[bottomExt] === 0) {
              hints.push({
                edgeIdx: bottomExt,
                state: -1,
                reason: `隣接する3のマスの隣に2のマスがあるため、3のマスの角から外へ逃げる辺は必ず×になります。`
              });
            }
          }

          // Subcase 2.3: 2 is left of top 3 at (r, c - 1)
          if (c - 1 >= 0 && this.clues[r][c - 1] === 2) {
            const leftOf2 = this.getVEdgeIndex(r, c - 1);
            if (leftOf2 !== -1 && this.edgeStates[leftOf2] === 0) {
              hints.push({
                edgeIdx: leftOf2,
                state: 1,
                reason: `隣接する3のマスの隣に2のマスがあるため、2のマスの対面の辺は必ず線になります。`
              });
            }
            const topExt = this.getVEdgeIndex(r - 1, c);
            if (topExt !== -1 && this.edgeStates[topExt] === 0) {
              hints.push({
                edgeIdx: topExt,
                state: -1,
                reason: `隣接する3のマスの隣に2のマスがあるため、3のマスの角から外へ逃げる辺は必ず×になります。`
              });
            }
          }

          // Subcase 2.4: 2 is left of bottom 3 at (r + 1, c - 1)
          if (c - 1 >= 0 && this.clues[r + 1][c - 1] === 2) {
            const leftOf2 = this.getVEdgeIndex(r + 1, c - 1);
            if (leftOf2 !== -1 && this.edgeStates[leftOf2] === 0) {
              hints.push({
                edgeIdx: leftOf2,
                state: 1,
                reason: `隣接する3のマスの隣に2のマスがあるため、2のマスの対面の辺は必ず線になります。`
              });
            }
            const bottomExt = this.getVEdgeIndex(r + 2, c);
            if (bottomExt !== -1 && this.edgeStates[bottomExt] === 0) {
              hints.push({
                edgeIdx: bottomExt,
                state: -1,
                reason: `隣接する3のマスの隣に2のマスがあるため、3のマスの角から外へ逃げる辺は必ず×になります。`
              });
            }
          }

        }
      }
    }
    return hints;
  }
  // --- RULE 26: 2と3が斜めに隣接し、2の外側の2辺のどちらかに×がある場合 ---
  checkDiagonal23WithExternalCross() {
    const hints = [];

    for (let r = 0; r < this.rows; r++) {
      for (let c = 0; c < this.cols; c++) {
        if (this.clues[r][c] !== 2) continue;

        const diagonals = [
          {
            // Bottom-Right: 3 is at (r+1, c+1)
            dr: 1, dc: 1,
            outer2H: this.getHEdgeIndex(r, c),
            outer2V: this.getVEdgeIndex(r, c),
            outer3H: this.getHEdgeIndex(r + 2, c + 1),
            outer3V: this.getVEdgeIndex(r + 1, c + 2)
          },
          {
            // Bottom-Left: 3 is at (r+1, c-1)
            dr: 1, dc: -1,
            outer2H: this.getHEdgeIndex(r, c),
            outer2V: this.getVEdgeIndex(r, c + 1),
            outer3H: this.getHEdgeIndex(r + 2, c - 1),
            outer3V: this.getVEdgeIndex(r + 1, c - 1)
          },
          {
            // Top-Right: 3 is at (r-1, c+1)
            dr: -1, dc: 1,
            outer2H: this.getHEdgeIndex(r + 1, c),
            outer2V: this.getVEdgeIndex(r, c),
            outer3H: this.getHEdgeIndex(r - 1, c + 1),
            outer3V: this.getVEdgeIndex(r - 1, c + 2)
          },
          {
            // Top-Left: 3 is at (r-1, c-1)
            dr: -1, dc: -1,
            outer2H: this.getHEdgeIndex(r + 1, c),
            outer2V: this.getVEdgeIndex(r, c + 1),
            outer3H: this.getHEdgeIndex(r - 1, c - 1),
            outer3V: this.getVEdgeIndex(r - 1, c - 1)
          }
        ];

        for (const diag of diagonals) {
          const r3 = r + diag.dr;
          const c3 = c + diag.dc;

          if (r3 >= 0 && r3 < this.rows && c3 >= 0 && c3 < this.cols) {
            if (this.clues[r3][c3] === 3) {
              const o2H = diag.outer2H;
              const o2V = diag.outer2V;
              const o3H = diag.outer3H;
              const o3V = diag.outer3V;

              const hIsCross = (o2H !== -1 && this.edgeStates[o2H] === -1);
              const vIsCross = (o2V !== -1 && this.edgeStates[o2V] === -1);

              if (hIsCross || vIsCross) {
                if (hIsCross && o2V !== -1 && this.edgeStates[o2V] === 0) {
                  hints.push({
                    edgeIdx: o2V,
                    state: 1,
                    reason: `2と3が斜めに隣接し、2の外側の辺の片方が×であるため、もう片方の辺は必ず線になります。`
                  });
                }
                if (vIsCross && o2H !== -1 && this.edgeStates[o2H] === 0) {
                  hints.push({
                    edgeIdx: o2H,
                    state: 1,
                    reason: `2と3が斜めに隣接し、2の外側の辺の片方が×であるため、もう片方の辺は必ず線になります。`
                  });
                }
                
                if (o3H !== -1 && this.edgeStates[o3H] === 0) {
                  hints.push({
                    edgeIdx: o3H,
                    state: 1,
                    reason: `2と3が斜めに隣接し、2の外側の辺に×があるため、3の外側の2辺は必ず両方とも線になります。`
                  });
                }
                if (o3V !== -1 && this.edgeStates[o3V] === 0) {
                  hints.push({
                    edgeIdx: o3V,
                    state: 1,
                    reason: `2と3が斜めに隣接し、2の外側の辺に×があるため、3の外側の2辺は必ず両方とも線になります。`
                  });
                }
              }
            }
          }
        }
      }
    }
    return hints;
  }

  // --- Main API Entrypoint ---
  static getHint(rows, cols, clues, edgeStates, solution, allowMulti = false) {
    const solver = new LoopCourseHintSolver(rows, cols, clues, edgeStates, solution);

    // Safety function: Ensure deduction does not contradict the pre-solved solution
    const isSafe = (edgeIdx, state) => {
      if (solution && solution[edgeIdx] !== state) {
        console.warn(`[HintSolver] Warning: deduced state ${state} for edge ${edgeIdx} contradicts solution ${solution[edgeIdx]}`);
        return false;
      }
      return true;
    };

    // --- SPECIAL CROSS-PHASE: AUTO-FILL ALL OBVIOUS CROSSES AT ONCE ---
    if (allowMulti) {
      const obviousCrosses = [];
      const seenEdges = new Set();

      // From cell constraints
      const cellCrosses = solver.checkCellConstraints().filter(h => h.state === -1 && isSafe(h.edgeIdx, -1));
      for (const h of cellCrosses) {
        if (!seenEdges.has(h.edgeIdx)) {
          seenEdges.add(h.edgeIdx);
          obviousCrosses.push({ edgeIdx: h.edgeIdx, state: -1 });
        }
      }

      // From dot constraints
      const dotCrosses = solver.checkDotConstraints().filter(h => h.state === -1 && isSafe(h.edgeIdx, -1));
      for (const h of dotCrosses) {
        if (!seenEdges.has(h.edgeIdx)) {
          seenEdges.add(h.edgeIdx);
          obviousCrosses.push({ edgeIdx: h.edgeIdx, state: -1 });
        }
      }

      // From adjacent 3s crosses (separating line extensions)
      const adj3sCrosses = solver.checkAdjacent3s().filter(h => h.state === -1 && isSafe(h.edgeIdx, -1));
      for (const h of adj3sCrosses) {
        if (!seenEdges.has(h.edgeIdx)) {
          seenEdges.add(h.edgeIdx);
          obviousCrosses.push({ edgeIdx: h.edgeIdx, state: -1 });
        }
      }

      if (obviousCrosses.length > 0) {
        return {
          isMulti: true,
          changes: obviousCrosses,
          state: -1,
          reason: `マスに既定の線が入っている箇所、ドットから線が2本出ている箇所、および隣接する3の境界の延長線上（合計 ${obviousCrosses.length} 箇所）の×をすべて埋めました。`
        };
      }
    }

    // --- PHASE 1: SEARCH FOR LINE HINTS (state === 1) ---
    const lineRules = [
      () => solver.checkCorner3(),
      () => solver.checkCorner2(),
      () => solver.checkCellConstraints(),
      () => solver.checkAdjacent3s(),
      () => solver.checkDiagonal3s(),
      () => solver.checkDiagonal323(),
      () => solver.check3CornerOutsideCrosses(),
      () => solver.check2CornerOutsideCrosses(),
      () => solver.check3OppositeLineFromTwoLines(),
      () => solver.checkAdjacent1sLinePropagation(),
      () => solver.checkAdjacent3And1WithOutsideCross(),
      () => solver.check2CornerLineCrossWithDiagonal3(),
      () => solver.check1CornerCrossesOppositeOutsideCross(),
      () => solver.check2CornerOutsidePropagation(),
      () => solver.check3CornerLineEntry(),
      () => solver.check3AdjacentTo0(),
      () => solver.checkDotConstraints(),
      () => solver.check2OppositeLineFromLineCross(),
      () => solver.checkAdjacent3sWith2(),
      () => solver.checkDiagonal23WithExternalCross()
    ];

    for (const rule of lineRules) {
      const candidates = rule();
      const lineCandidates = candidates.filter(h => h.state === 1 && isSafe(h.edgeIdx, 1));
      if (lineCandidates.length > 0) {
        return lineCandidates[0]; // Return the first line hint
      }
    }

    // --- PHASE 2: SEARCH FOR CROSS HINTS (state === -1) ---
    const crossRules = [
      () => solver.checkAround0(),
      () => solver.checkCorner1(),
      () => solver.check1CornerOutsideCrosses(),
      () => solver.checkAdjacent3s(), // Adjacent 3s has cross extensions
      () => solver.check2CornerOutsideCrosses(),
      () => solver.check3CornerLineEntry(),
      () => solver.check1CornerOutsideCrossesOppositeEntry(),
      () => solver.check2OppositeCrossFromLineCross(),
      () => solver.check3OppositeCrossFromTwoLines(),
      () => solver.check1CornerLineEntry(),
      () => solver.checkAdjacent3And1WithOutsideCross(),
      () => solver.check3CornerLinesWithDiagonal1(),
      () => solver.checkDiagonal1sOutsideCrosses(),
      () => solver.check2CornerOutsidePropagation(),
      () => solver.checkCellConstraints(),
      () => solver.checkDotConstraints(),
      () => solver.checkPrematureLoops(),
      () => solver.checkAdjacent3sWith2()
    ];

    for (const rule of crossRules) {
      const candidates = rule();
      const crossCandidates = candidates.filter(h => h.state === -1 && isSafe(h.edgeIdx, -1));
      if (crossCandidates.length > 0) {
        return crossCandidates[0]; // Return the first cross hint
      }
    }

    // --- PHASE 3: FALLBACK TO LOOK-AHEAD (仮定法) ---
    // Try to find any edge that MUST be a line (meaning setting to cross causes contradiction)
    for (let i = 0; i < solver.numEdges; i++) {
      if (solver.edgeStates[i] === 0) {
        if (solver.testContradiction(i, -1)) {
          if (isSafe(i, 1)) {
            return {
              edgeIdx: i,
              state: 1,
              reason: `仮にこの辺を×と仮定すると、周囲の制約またはマスの数字で矛盾が生じるため、ここは線になります（仮定法による先読み）。`
            };
          }
        }
      }
    }

    // Try to find any edge that MUST be a cross (meaning setting to line causes contradiction)
    for (let i = 0; i < solver.numEdges; i++) {
      if (solver.edgeStates[i] === 0) {
        if (solver.testContradiction(i, 1)) {
          if (isSafe(i, -1)) {
            return {
              edgeIdx: i,
              state: -1,
              reason: `仮にこの辺に線を引くと仮定すると、周囲の制約またはマスの数字で矛盾が生じるため、ここは×になります（仮定法による先読み）。`
            };
          }
        }
      }
    }

    return null; // No logical hint found
  }
}

// Bind to global scope
if (typeof self !== 'undefined') {
  self.LoopCourseHintSolver = LoopCourseHintSolver;
} else if (typeof window !== 'undefined') {
  window.LoopCourseHintSolver = LoopCourseHintSolver;
} else {
  globalThis.LoopCourseHintSolver = LoopCourseHintSolver;
}
