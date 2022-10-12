#!/usr/bin/env python3

import subprocess
import sys, os
from os.path import abspath
from pathlib import Path
from typing import Tuple, List
import re
from enum import Enum
from collections import defaultdict
from functools import reduce

servois2_dir = './'
yml_dir = './yamls/'

servois2 = servois2_dir + 'src/servois2'

TIMEOUT = 30

N_TRIALS = 1

# TODO: speedup of poke2-lattice over poke? poke2 over poke?

class Heuristic(Enum):
    SIMPLE = 0
    POKE = 11
    POKE2 = 21
    POKE2_LATTICE = 22
    MC_MAX = 31
    MC_MAX_LATTICE = 32
    MC_BISECT = 41
    MC_BISECT_LATTICE = 42
    
    def __str__(self):
        return string_of_heuristic[self]

string_of_heuristic = {
    Heuristic.SIMPLE: "simple",
    Heuristic.POKE: "poke",
    Heuristic.POKE2: "poke2",
    Heuristic.POKE2_LATTICE: "poke2-lattice",
    Heuristic.MC_MAX: "mc-max",
    Heuristic.MC_MAX_LATTICE: "mc-max-lattice",
    Heuristic.MC_BISECT: "mc-bisect",
    Heuristic.MC_BISECT_LATTICE: "mc-bisect-lattice"
}

command_of_heuristic = {
    Heuristic.SIMPLE: [],
    Heuristic.POKE: ["--poke"],
    Heuristic.POKE2: ["--poke2"],
    Heuristic.POKE2_LATTICE: ["--poke2", "--lattice"],
    Heuristic.MC_MAX: ["--mcpeak-max"],
    Heuristic.MC_MAX_LATTICE: ["--mcpeak-max", "--lattice"],
    Heuristic.MC_BISECT: ["--mcpeak-bisect"],
    Heuristic.MC_BISECT_LATTICE: ["--mcpeak-bisect", "--lattice"]
}

class AdditionalOptions(Enum):
    LEFT_MOVER = 0
    RIGHT_MOVER = 1
    
    def __str__(self):
        return string_of_options[self]
    
string_of_options = {
    AdditionalOptions.LEFT_MOVER:  "--leftmover",
    AdditionalOptions.RIGHT_MOVER: "--rightmover"
}

benches_type = defaultdict(lambda: str, {
    'predicates': int,
    'predicates_filtered': int,
    'smtqueries': int,
    'mcqueries': int,
    'time_lattice_construct': float,
    'time_mc_run': float,
    'time_synth': float,
    'time': float
})

class TestCase():
    def __init__(self, heuristic, opts = ()):
        self.heuristic = heuristic
        self.opts = opts
        self.ran = False
    def run(self, yml, m, n):
        command_infer = [
            servois2, 'synth', '-q',
            '--timeout', str(TIMEOUT), '--prover', 'cvc4'
        ] + list(map(str, self.opts)) + command_of_heuristic[self.heuristic] + [yml_dir + yml, m, n]
        sys.stdout.write(f'Running command: {str(command_infer)}\n')
        try:
            benches = defaultdict(float) # Doesn't only contain floats, but only will blindly query for them.
            for x in range(N_TRIALS):
                stdout, stderr = run_command(command_infer)
                result, benches_trial = process_output(stdout, stderr)
                for bench in benches_trial:
                    res = benches_type[bench](benches_trial[bench])
                    if benches_type[bench] is float:
                        benches[bench] += res
                    elif bench not in benches:
                        benches[bench] = res
            if not "time" in benches: raise Exception(stdout, stderr)
            benches = { k: v/N_TRIALS if benches_type[k] is float else v for (k, v) in benches.items() }
        except Exception as err:
            result = "false"
            benches = None
            sys.stdout.write(f'\nFailure: {str(err.args)}\n')

        sys.stdout.write(f'Done.\n')
        sys.stdout.flush()

        self.res = result
        self.benches = benches
        self.ran = True
    def __str__(self):
        return str((str(self.heuristic),) + tuple(map(str, self.opts)))

def make_all_heuristics(test_dict): # -> dict[str, dict[tuple[str, str], list[TestCase]]]:
    return {
        yml: {
            (ms[0], ms[1]): [TestCase(h, ms[2:]) for h in string_of_heuristic]
            for ms in test_dict[yml]
            }
        for yml in test_dict
        }

def make_gen_heuristics(test_dict):
    return {
        yml: {
            (ms[0], ms[1]): [
                TestCase(h, ms[2:])
                for h in {Heuristic.SIMPLE, Heuristic.POKE, Heuristic.POKE2, Heuristic.POKE2_LATTICE}
                ]
            for ms in test_dict[yml]
            }
        for yml in test_dict
        }

name_of_yml = {
    'string.yml': 'Str',
    'lia.yml': 'LIA',
    'set.yml': 'Set',
    'hashtable.yml': 'HT',
    'stack.yml': 'Sta'
}

table1_heuristics = [Heuristic.POKE, Heuristic.POKE2, Heuristic.MC_MAX]

table2_heuristics = [Heuristic.POKE2, Heuristic.POKE2_LATTICE, Heuristic.MC_MAX, Heuristic.MC_MAX_LATTICE]

testcases = {
    # First, the cases that are to be run on /all/ heuristics (LIA and String)
    ** make_all_heuristics({
        'string.yml': [
            ('substr', 'hasChar'),
            ('substr', 'isEmpty'),
            ('hasChar', 'concat')
        ],
        'lia.yml': [
            ('sum', 'posSum'),
            ('sum', 'multiVarSum'),
            ('multiVarCondA', 'multiVarCondB')
        ]
    }),
    # Second, the cases that are to be run on non-mc heuristics only.
    ** make_gen_heuristics({
        'set.yml': [
            ('add', 'add'),
            ('add', 'contains'),
            ('add', 'getsize'),
            ('add', 'remove'),
            ('contains', 'remove'),
            ('getsize', 'remove'),
            ('remove', 'remove')
            ],
        'hashtable.yml': [
            ('get', 'put', AdditionalOptions.RIGHT_MOVER),
            ('put', 'get', AdditionalOptions.RIGHT_MOVER),
            ('get', 'remove', AdditionalOptions.RIGHT_MOVER),
            ('haskey', 'put'),
            ('haskey', 'remove'),
            ('put', 'put'),
            ('put', 'remove'),
            ('put', 'size'),
            ('remove', 'remove'),
            ('remove', 'size')
            ],
        'stack.yml' : [
            ('pop', 'pop'),
            ('push', 'pop', AdditionalOptions.RIGHT_MOVER),
            ('pop', 'push', AdditionalOptions.RIGHT_MOVER),
            ('push', 'push')
            ]
    })
}

def process_output(stdout, stderr):
    try:
        res = latex_of_phi(stdout)
        benches = dict(line.split(', ') for line in stderr.strip().split('\n'))
    except:
        raise Exception(stdout, stderr)
    return res, benches

# LaTeX utilities:
NA_STRING = '--'

def latex_tt(s : str) -> str:
    return f'\\texttt{{{s}}}'

def latex_of_time(t : float):
    return f'{t:#.2f}'

op_map = {
    '==': '!=',  '!=': '==',
    '<': '>=',   '>=': '<',
    '>': '<=',   '<=': '>'
}
op_map_escaped = {
    re.escape(k): re.escape(v) 
    for k,v in op_map.items()
}

re_ops = '|'.join(map(re.escape, op_map_escaped.keys()))
re_term = r'.*?'

re_neg_match = re.compile(
    fr''' ! \s? \( 
        \s? (?P<arg1>{re_term}) \s? 
        (?P<op>{re_ops}) \s? 
        (?P<arg2>{re_term}) \s? \) 
        ''',
    re.X
)

def re_neg_goal(r : re.Match) -> str:
    arg1 = r.group('arg1')
    op   = r.group('op')
    arg2 = r.group('arg2')
    res = f'{arg1} {op_map[op]} {arg2}'
    return res

# https://texblog.net/latex-archive/uncategorized/symbols/
def latex_escape(s : str):
    s = s.replace('#', '\\#')
    s = s.replace('$', '\\$')
    s = s.replace('%', '\\%')
    s = s.replace('_', '\\_')
    s = s.replace('&', '\\&')
    s = s.replace('{', '\\{')
    s = s.replace('}', '\\}')
    s = s.replace('^', '\\^{}')
    s = s.replace('||', '\\textbar\\textbar\\ ')
    s = s.replace('> ', '\\textgreater\\ ')
    s = s.replace('< ', '\\textless\\ ')
    return s

## Replaces '!(_ op _)' with '_ !op _'
def latex_of_exp(exp : str, abridge=False) -> str:
    exp = re.sub(re_neg_match, re_neg_goal, exp)
    if abridge:
        l = exp.split('||')
        if len(l) > 2:
            exp = f'{l[0]}|| ... ||{l[-1]}'
    return exp

def latex_of_phi(phi, abridge=False) -> str:
    if not phi:
        return NA_STRING
    p = latex_of_exp(phi, abridge)
    p = latex_escape(p)
    p = latex_tt(p)
    return p

def string_of_ms(ms):
    if len(ms) > 2:
        if ms[2] is AdditionalOptions.LEFT_MOVER:
            return ms[1] + ' $ \\rrrm $ ' + ms[0]
        else:
            return ms[0] + ' $ \\rrrm $ ' + ms[1]
    else:
        return ms[0] + ' $ \\bowtie $ ' + ms[1]

mkheader = lambda cols : (
    "\\begin{table} \\begin{tabular}{|l|c|" + '|'.join(["r" for _ in cols]) + "|} \\hline\n" +
    "\\bf{ADT} & \\bf{Methods} & " + ' & '.join(f'\\bf{{{str(h)}}}' for h in cols) + "\\\\\n"
)

table1_header = mkheader(table1_heuristics)

table1_footer = (
    "\\hline\n"+
    "\\end{tabular}\n" +
    "\\\\\n" +
    "\\caption{\\label{table:one}Total execution time comparison between \\poke{} and new heuristics. Speedup relative to \\poke{} is given in parentheses. All times are given in seconds.}\n" +
    "\\end{table}\n"
)

def find_result(yml, ms, reslist, heuristic):
    for t in reslist:
        if t.heuristic is heuristic:
            if not t.ran: t.run(yml, ms[0], ms[1]) # Run test cases lazily
            return t.benches
    else:
        return None

prod = lambda l: reduce(lambda x, y: x * y, l, 1)
geomean = lambda l: prod(l) ** (1 / len(l)) if l else 1

def make_table1(cases):
    table = table1_header
    # Speedup relative to poke
    poke2_speedup = []
    mc_max_speedup = []
    for yml in cases:
        section = "\\hline\n" + name_of_yml[yml]
        for ms in cases[yml]:
            results = cases[yml][ms]
            row_heurs = defaultdict(lambda: None)
            for heur in table1_heuristics:
                try:
                    row_heurs[heur] = find_result(yml, ms, results, heur)["time"]
                except:
                    pass
            poke2_speedup.append(row_heurs[Heuristic.POKE] / row_heurs[Heuristic.POKE2])
            if Heuristic.MC_MAX in row_heurs:
                mc_max_speedup.append(row_heurs[Heuristic.POKE] / row_heurs[Heuristic.MC_MAX])
            def str_of_heur(h):
                try:
                    if h is min(row_heurs, key=row_heurs.get):
                        if h is Heuristic.POKE: return "\\bf{{{:.2f}}}".format(row_heurs[h])
                        else: return "\\bf{{{:.2f}}}({:.1f}$\\times$)".format(row_heurs[h], row_heurs[Heuristic.POKE] / row_heurs[h])
                    else:
                        if h is Heuristic.POKE: return "{:.2f}".format(row_heurs[h])
                        else: return "{:.2f}({:.1f}$\\times$)".format(row_heurs[h], row_heurs[Heuristic.POKE] / row_heurs[h])
                except: return NA_STRING
            section += f' & {string_of_ms(ms)} & ' + ' & '.join([str_of_heur(h) for h in table1_heuristics]) + "\\\\\n"
        table += section
    table += table1_footer
    # TODO: We're taking the geomean across potentially the arithmetic mean of individual trials. Invalid?
    table += (
        "\\newcommand{{\\poketwospeedup}}{:.1f}\n".format(geomean(poke2_speedup)) + 
        "\\newcommand{{\\mcmaxspeedup}}{:.1f}\n".format(geomean(mc_max_speedup))
    )
    return table

is_lattice = defaultdict(lambda: False, {
    Heuristic.POKE2_LATTICE: True,
    Heuristic.MC_MAX_LATTICE: True,
    Heuristic.MC_BISECT_LATTICE: True
    }
)

table2_header = mkheader(table2_heuristics)
table2_footer = (
    "\\hline\n"+
    "\\end{tabular}\n" +
    "\\\\\n" +
    "\\caption{\\label{table:two}Comparison of times taken with use of the predicate lattice. Time in parentheses is synth only time. All times are given in seconds.}\n" +
    "\\end{table}\n"
)

def make_table2(cases):
    table = table2_header
    for yml in cases:
        section = "\\hline\n" + name_of_yml[yml]
        for ms in cases[yml]:
            def time(h):
                tmp = find_result(yml, ms, cases[yml][ms], h)
                if tmp:
                    if is_lattice[h]:
                        return "{:.2f}(\\textbf{{{:.2f}}})".format(tmp["time"], tmp["time_synth"])
                    else:
                        return "{:.2f}".format(tmp["time"])
                else: return NA_STRING
            section += f' & {string_of_ms(ms)} & ' + ' & '.join([time(h) for h in table2_heuristics]) + "\\\\\n"
        table += section
        
    # Calc spedups
    poke2_lattice_speedup = []
    mc_max_lattice_speedup = []
    for yml in cases:
        for ms in cases[yml]:
            pokeres = find_result(yml, ms, cases[yml][ms], Heuristic.POKE)
            poke2res = find_result(yml, ms, cases[yml][ms], Heuristic.POKE2_LATTICE)
            mcmaxres = find_result(yml, ms, cases[yml][ms], Heuristic.MC_MAX_LATTICE)
            if not pokeres: continue
            if poke2res: poke2_lattice_speedup.append(pokeres["time"] / poke2res["time"])
            if mcmaxres: mc_max_lattice_speedup.append(pokeres["time"] / mcmaxres["time"])
    
    table += (
        "\\newcommand{{\\poketwolatticespeedup}}{:.1f}\n".format(geomean(poke2_lattice_speedup)) + 
        "\\newcommand{{\\mcmaxlatticespeedup}}{:.1f}\n".format(geomean(mc_max_lattice_speedup))
    )
    
    table += table2_footer
    return table

def run_command(command : List[str]):
    popen = subprocess.Popen(
        command, universal_newlines=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    out, err = popen.communicate()
    if 'error' in err or 'exception' in err:
        raise Exception(err)
    return out, err


if __name__ == '__main__':
    if len(sys.argv) > 1:
        N_TRIALS = int(sys.argv[1])
    table1 = make_table1(testcases)
    with open("benchmarks_1.tex", 'w') as f:
        f.write(table1)
    table2 = make_table2(testcases)
    with open("benchmarks_2.tex", 'w') as f:
        f.write(table2)
