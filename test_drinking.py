#!/bin/env python3
# For Assignment 2 (CSC 258) - Spring 2019
# Author: Princeton Ferro <pferro@u.rochester.edu>

import re
import sys

graph = {}

if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(prog=sys.argv[0])
    parser.add_argument('graph')
    parser.add_argument('output')

    args = parser.parse_args()

    f_graph = open(args.graph, 'r')
    lineno = 0
    num_philosophers = 0
    for line in f_graph:
        lineno = lineno + 1
        m = re.match(r'(\d+)\s*(\d+)', line)
        if not m:
            if lineno == 1:
                num_philosophers = int(line)
                print(f'Okay, there are {num_philosophers} philosophers')
            continue
        p1_str, p2_str = m.groups()
        p1, p2 = int(p1_str), int(p2_str)

        if p1 not in range(1, num_philosophers+1):
            raise Exception(f'{args.graph}:{lineno} !(1 <= p1 <= {num_philosophers})')

        if p2 not in range(1, num_philosophers+1):
            raise Exception(f'{args.graph}:{lineno} !(1 <= p2 <= {num_philosophers})')

        if p1 not in graph:
            graph[p1] = [p2]
        else:
            graph[p1].append(p2)

        if p2 not in graph:
            graph[p2] = [p1]
        else:
            graph[p2].append(p1)

    f_graph.close()

    # check for connectivity
    visited = {p: False for p in range(1, num_philosophers+1)}
    queue = [1]

    while queue:
        p = queue.pop(0)

        visited[p] = True
        for n in graph[p]:
            if not visited[n]:
                queue.append(n)

    for p in range(1, num_philosophers+1):
        if not visited[p]:
            raise Exception(f'{p} is not connected to the rest of the graph ' + str({n for n in range(1, num_philosophers+1) if visited[n]}))

    # evaluate output
    f_output = open(args.output, 'r')
    drinking = {p: False for p in range(1, num_philosophers+1)}
    lineno = 0
    for line in f_output:
        lineno = lineno + 1
        m = re.match(r'philosopher (\d+) (\w+)', line)
        if not m:
            raise Exception(f'{args.output}:{lineno}: malformed input')
        p_str, status = m.groups()
        if not (status == 'drinking' or status == 'thinking'):
            raise Exception(f'{args.output}:{lineno}: malformed input, expected either "drinking" or "thinking"')
        p = int(p_str)
        if not (p >= 1 and p <= num_philosophers):
            raise Exception(f'{args.output}:{lineno}: malformed input, !(1 <= p <= {num_philosophers})')

        drinking[p] = status == 'drinking'
        if drinking[p]:
            for n in graph[p]:
                if drinking[n]:
                    sys.exit(f'{args.output}:{lineno}: philosopher #{p} attempts to drink from a bottle that philosopher #{n} is currently drinking from!')
    f_output.close()

    print('Everything looks good to me.')
