# json2dir-bcpl

json2dir in BCPL: a Cintcode BCPL evaluator (`json2dir.b`) validates the JSON and emits a shell script, which a small POSIX sh launcher runs.

    cintsys -c "bcpl json2dir.b to out/json2dir" && JSON2DIR_BCPL=/path/to/BCPL/cintcode ./json2dir < tree.json
