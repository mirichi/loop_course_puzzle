const fs = require('fs');
const path = require('path');
const createLoopCourseModule = require('./js/loopcourse.js');

async function main() {
    const args = process.argv.slice(2);
    if (args.length < 1) {
        console.error("Usage: node analyze_pencilbox.js <path_to_pencilbox_file.txt>");
        process.exit(1);
    }

    const filePath = args[0];
    const fileName = path.basename(filePath, path.extname(filePath));
    console.log(`Loading PencilBox file: ${filePath}`);

    const text = fs.readFileSync(filePath, 'utf8').trim();
    const lines = text.split('\n').map(l => l.trim()).filter(l => l.length > 0);

    if (lines.length < 3) {
        console.error("Invalid file format. Need at least rows, cols, and grid data.");
        process.exit(1);
    }

    const rows = parseInt(lines[0], 10);
    const cols = parseInt(lines[1], 10);

    console.log(`Detected Grid Size: ${rows}x${cols}`);

    // Parse clues
    const parsedClues = new Int8Array(rows * cols);
    parsedClues.fill(-1);

    let cellIdx = 0;
    for (let i = 2; i < 2 + rows; i++) {
        if (!lines[i]) break;
        const tokens = lines[i].split(/\s+/);
        for (let j = 0; j < cols; j++) {
            if (tokens[j] === undefined || tokens[j] === '.') {
                parsedClues[cellIdx] = -1;
            } else {
                parsedClues[cellIdx] = parseInt(tokens[j], 10);
            }
            cellIdx++;
        }
    }

    const Module = await createLoopCourseModule();

    // Wrap C functions
    const init_grid = Module.cwrap('init_grid', null, ['number', 'number']);
    const get_clues_ptr = Module.cwrap('get_clues_ptr', 'number', []);
    const analyze_puzzle = Module.cwrap('analyze_puzzle', 'number', ['string']);
    const get_ac3_rule_name = Module.cwrap('get_ac3_rule_name', 'string', ['number']);
    const get_deduction_log_count = Module.cwrap('get_deduction_log_count', 'number', []);
    const get_deduction_logs_ptr = Module.cwrap('get_deduction_logs_ptr', 'number', []);
    // Initialize WASM state
    init_grid(rows, cols);

    // Write clues into WASM memory
    const cluesPtr = get_clues_ptr();
    for (let i = 0; i < rows * cols; i++) {
        Module.HEAP8[cluesPtr + i] = parsedClues[i];
    }

    console.log(`\n--- Running Analyzer on ${fileName} ---`);
    const start_time = performance.now();
    const result = analyze_puzzle("Master");
    const end_time = performance.now();
    console.log(`[Analyzer] analyze_puzzle returned: ${result}`);

    const get_perf_lookahead = Module.cwrap('get_perf_lookahead', 'number', []);

    // Fetch and aggregate all rule times
    const get_ac3_rule_time = Module.cwrap('get_ac3_rule_time', 'number', ['number']);
    const get_ac3_rule_hit_count = Module.cwrap('get_ac3_rule_hit_count', 'number', ['number']);

    const ruleTimes = [];
    let totalAC3Time = 0;

    for (let id = 100; id <= 250; id++) {
        const name = get_ac3_rule_name(id);
        if (name) {
            const time = get_ac3_rule_time(id);
            const hits = get_ac3_rule_hit_count(id);
            if (time > 0 || hits > 0) {
                ruleTimes.push({ id, name, time, hits });
                totalAC3Time += time;
            }
        }
    }

    ruleTimes.sort((a, b) => b.time - a.time); // Sort by time descending

    console.log(`[Analyzer] Total analysis time: ${(end_time - start_time).toFixed(2)} ms`);
    console.log(`\n=== Rule Execution Times ===`);
    for (const t of ruleTimes) {
        console.log(`${t.name.padEnd(35)} : ${t.time.toFixed(2).padStart(8)} ms | ${t.hits.toString().padStart(6)} hits`);
    }
    console.log('--------------------------------------------------');
    console.log(`Total Rule Processing Time          : ${totalAC3Time.toFixed(2).padStart(8)} ms`);
    console.log(`Total Lookahead Assumption Time     : ${get_perf_lookahead().toFixed(2).padStart(8)} ms`);

    // Dump to specific CSV file
    const count = get_deduction_log_count();
    const ptr = get_deduction_logs_ptr();

    let HEAP32 = new Int32Array(Module.HEAP8.buffer);
    let csvData = "Step,EdgeIdx,RuleID,Difficulty,RuleName,LookaheadDepth,State\n";
    for (let i = 0; i < count; i++) {
        let edgeIdx = HEAP32[(ptr >> 2) + i * 4 + 0];
        let ruleId = HEAP32[(ptr >> 2) + i * 4 + 1];
        let depth = HEAP32[(ptr >> 2) + i * 4 + 2];
        let state = HEAP32[(ptr >> 2) + i * 4 + 3];
        let ruleName = get_ac3_rule_name(ruleId);

        let diff = -1;
        if (ruleId >= 101 && ruleId <= 109) diff = 1;
        else if (ruleId >= 111 && ruleId <= 119) diff = 2;
        else if (ruleId >= 121 && ruleId <= 129) diff = 3;
        else if (ruleId >= 131 && ruleId <= 140) diff = 4;
        else if (ruleId == 143 || ruleId == 145 || ruleId == 153) diff = 6;
        else if (ruleId >= 141 && ruleId <= 149) diff = 5;
        else if (ruleId == 151 || ruleId == 155) diff = 9;
        else if (ruleId == 154) diff = 8;
        else if (ruleId >= 152 && ruleId <= 159) diff = 7;
        else if (ruleId >= 161 && ruleId <= 169) diff = 8;
        else if (ruleId == 200 || ruleId == 201 || depth > 0) diff = 10 + depth;
        else diff = ruleId;

        // step is just i+1 since we don't store it in the struct
        csvData += `${i + 1},${edgeIdx},${ruleId},${diff},"${ruleName}",${depth},${state}\n`;
    }

    const outCsv = `${fileName}_deduction.csv`;
    fs.writeFileSync(outCsv, csvData);
    console.log(`[Analyzer] Dumped ${count} deduction steps to '${outCsv}'.`);
    const get_edge_states_ptr = Module.cwrap('get_edge_states_ptr', 'number', []);
    const edgesPtr = get_edge_states_ptr();
    const numEdges = (rows + 1) * cols + rows * (cols + 1);
    const edges = new Int8Array(Module.HEAP8.buffer, edgesPtr, numEdges);
    let unknown = 0;
    for (let i = 0; i < numEdges; i++) if (edges[i] == 0) unknown++;
    console.log('Unknown edges:', unknown);
    // We could check if there are unresolved edges by calling something, 
    // but the CSV step count gives us a hint anyway.
}

main().catch(err => {
    console.error(err);
    process.exit(1);
});
