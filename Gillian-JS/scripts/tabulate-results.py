#!/usr/bin/env python3

import argparse
import json
import sys
import re

from tabulate import tabulate
from pathlib import Path


def list_directories(path):
    p = Path(path)
    try:
        return sorted([child.resolve() for child in p.iterdir() if child.is_dir()])
    except FileNotFoundError:
        print(f"Path '{path}' not found.")
        return []


def split_results_dir(path: str | Path):
    if isinstance(path, Path):
        path = path.name

    regex = r'results-(.+)-(([^\d]+).+)\.?'

    match = re.search(regex, path)
    if match:
        objmodel = match.group(1)
        testname = match.group(2)
        testgroup = match.group(3)
        return objmodel, testgroup, testname


def read_json_file(path):
    with open(path, 'r') as f:
        return json.load(f)


def write_json_file(path, data):
    with open(path, "w") as f:
        json.dump(data, f, indent=2)


def save_table(outdir: Path, name: str | Path, table: str, log=True):
    file = outdir / name
    with open(file, "w") as f:
        f.write(table)
    if log:
        print(f'Table saved: {file}')


def create_entry(key: str, obj: dict):
    entry = {
        'time': 0.0,
        'solver_time': 0.0,
        'solver_queries': 0,
        'paths': 0,
        'exec_cmds': 0,
        'ite_created': 0,
        'ite_unfolded': 0,
    }
    obj[key] = entry
    return entry


def create_top_entry(key: str, obj: dict):
    entry = create_entry(key, obj)
    entry['tests'] = {}
    return entry


def sum_entries(e1: dict, e2: dict) -> dict:
    for k in set(e1) & set(e2):
        e1[k] += e2[k]


def parse_benchmarks(results: str | Path):
    ret = {}
    results = Path(results)
    folders = list_directories(results)

    for folder in folders:
        objmodel, testgroup, testname = split_results_dir(folder.name)

        # --- Model level
        objmodel_entry = ret.get(objmodel)
        if objmodel_entry is None:
            objmodel_entry = create_top_entry(objmodel, ret)
        objmodel_tests = objmodel_entry['tests']

        # --- Group level
        folder_entry = objmodel_tests.get(testgroup)
        if folder_entry is None:
            folder_entry = create_top_entry(testgroup, objmodel_tests)
        folder_tests = folder_entry['tests']

        assert testname not in folder_tests, f"Duplicate test name: {testname}"

        # --- Read stats
        stats_path = folder / 'stats.json'
        if not stats_path.is_file():
            folder_tests[testname] = 'Error'
        else:
            stats = read_json_file(stats_path)
            # --- Accumulate
            sum_entries(objmodel_entry, stats)
            sum_entries(folder_entry, stats)
            test_entry = create_entry(testname, folder_tests)
            sum_entries(test_entry, stats)
    return ret


def _tabulate(results):
    header = ("Results",
              "Time",
              "Solver Time",
              "Solver Queries",
              "Paths",
              "Stmts",
              "ITEs Created",
              "ITEs Unfolded")

    return tabulate(results, headers=header, tablefmt="simple")


def _ncols(obj: dict):
    for v in obj.values():
        return len(v.keys())
    return 0


def _get_stats(obj: dict, digits=2):
    t = round(obj["time"], digits)
    st = round(obj["solver_time"], digits)
    sq = obj["solver_queries"]
    p = obj["paths"]
    ec = obj["exec_cmds"]
    itec = obj["ite_created"]
    iteu = obj["ite_unfolded"]
    return [t, st, sq, p, ec, itec, iteu]


def _get_tests(obj: dict):
    return obj["tests"]


def _table_rows(data: dict, ncols: int) -> list[list]:
    if not isinstance(data, dict) or not data:
        return []

    table = []
    for objmodel, objdata in data.items():
        try:
            stats = _get_stats(objdata)
        except Exception:
            stats = ["Error"] + ['---'] * ncols
        table.append([objmodel, *stats])

    return table


def tabulate_benchmarks(data: dict):
    ncols = _ncols(data) - 1
    model_table = _table_rows(data, ncols)
    detailed_tables = {}

    for objmodel, objdata in data.items():
        tests = _get_tests(objdata)
        assert tests is not None
        detailed_tables[objmodel] = []

        for group, group_data in tests.items():
            total = f'Total - {group}'
            group_total = [total] + _get_stats(group_data)
            group_tests = _get_tests(group_data)
            assert group_tests is not None

            details = _table_rows(group_tests, ncols)
            detailed_tables[objmodel] += (details)
            detailed_tables[objmodel].append(['--------'] * (ncols + 1))
            detailed_tables[objmodel].append(group_total)
            detailed_tables[objmodel].append(['--------'] * (ncols + 1))

    return model_table, detailed_tables


def parse_args():
    parser = argparse.ArgumentParser(
        description="Tabulate benchmarking results")

    parser.add_argument(
        "results",
        metavar="path",
        type=str,
        help="Path to the results directory / JSON file."
    )
    parser.add_argument(
        "-save-json",
        "-sj",
        action="store_true",
        help="Save a JSON file with the condensed reasults"
    )
    parser.add_argument(
        "--out",
        "-o",
        metavar="folder",
        default=".",
        type=str,
        help="Path where the tables should be saved"
    )
    return parser.parse_args()


def main():
    args = parse_args()
    results: Path = Path(args.results)
    out: Path = Path(args.out)
    save_json: bool = args.save_json

    if results.is_dir():
        condensed = parse_benchmarks(results)
        if save_json:
            filename = out / f'{results.name}.json'
            write_json_file(filename, condensed)
    else:
        assert results.is_file and results.name.endswith('.json')
        condensed = read_json_file(results)

    global_table, detailed_tables = tabulate_benchmarks(condensed)
    save_table(out, 'objmodels-table.txt', _tabulate(global_table))

    for k, v in detailed_tables.items():
        t = _tabulate(v)
        save_table(out, f'{k}-table.txt', t)

    sys.exit(0)


if __name__ == "__main__":
    main()
