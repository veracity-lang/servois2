#!/usr/bin/env python3

import subprocess
import sys, os
from os.path import abspath
from pathlib import Path
from typing import Tuple, List
import re
from enum import Enum

servois2_dir = './'
yml_dir = './yamls/'

servois2 = servois2_dir + 'src/servois2'

timeout = 30

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
    Heuristic.MC_MAX: ["--mcpeak-maxcover"],
    Heuristic.MC_MAX_LATTICE: ["--mcpeak-maxcover", "--lattice"],
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

class TestCase():
    def __init__(self, heuristic, opts = ()):
        self.heuristic = heuristic
        self.opts = opts
        self.ran = False
    def run(self, yml, m, n):
        command_infer = [
            servois2, 'synth', '-q',
            '--timeout', str(timeout), '--prover', 'cvc4'
        ] + list(map(str, self.opts)) + command_of_heuristic[self.heuristic] + [yml_dir + yml, m, n]
        sys.stdout.write(f'Running command: {str(command_infer)}\n')
        try:
            stdout, stderr = run_command(command_infer)
            result, time = process_output(stdout, stderr)
        except Exception as err:
            result = "false"
            time = None
            sys.stdout.write(f'\nFailure: {str(err.args)}\n')

        sys.stdout.write(f'Done.\n')
        sys.stdout.flush()

        self.res = result
        self.time = time
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

table_heuristics = [Heuristic.POKE, Heuristic.POKE2, Heuristic.POKE2_LATTICE, Heuristic.MC_MAX_LATTICE]

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
        benches = [line.split(', ') for line in stderr.split()]
        time = float(benches[-1][-1])
    except:
        raise Exception(stdout, stderr)
    return res, time

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

table_header = (
    "\\renewcommand{\\arraystretch}{\\benchtablerowstretch}\\setlength{\\tabcolsep}{\\benchtabletabcolsep}\\footnotesize" +
    "\\begin{table} \\begin{tabular}{|l|c|" + '|'.join(["r" for _ in table_heuristics]) + "|} \\hline" +
    "ADT & Methods & " + ' & '.join(str(h) for h in table_heuristics) + "\\\\\n"
)

table_footer = (
    "\\end{tabular} \\end{table}"
)

def find_result(yml, ms, reslist, heuristic):
    for t in reslist:
        if t.heuristic is heuristic:
            if not t.ran: t.run(yml, ms[0], ms[1]) # Run test cases lazily
            return "{:.3f}".format(t.time) if t.time else NA_STRING
    else:
        return NA_STRING

def make_table(cases):
    table = table_header
    for yml in cases:
        section = name_of_yml[yml]
        for ms in cases[yml]:
            results = cases[yml][ms]
            fr = lambda h: find_result(yml, ms, results, h)
            section += f' & {string_of_ms(ms)} & ' + ' & '.join([fr(h) for h in table_heuristics]) + "\\\\\n"
        table += section
    table += table_footer
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
    table = make_table(testcases)
    with open("benchmarks.tex", 'w') as f:
        f.write(table)
