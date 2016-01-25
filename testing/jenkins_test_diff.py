#!/usr/bin/env python3
import sys
import json
from collections import defaultdict
import urllib.request, urllib.parse

_, build_number_old, build_number_new = sys.argv

print('Comparing jenkins build {0} and {1}'.format(build_number_old, build_number_new))

state_renaming = {
        'PASSED': 'Pass',
        'REGRESSION': 'Fail',
        'FAILED': 'Fail',
        'FIXED': 'Pass',
        'SKIPPED': 'Skip',
        }

def get_test_results(build_no):
    url = 'http://compile.logic.tuwien.ac.at/job/{0}/{1}/testReport/api/json?tree=suites[cases[className,name,status]]' \
            .format(*map(urllib.parse.quote, [ 'gapt extended testing', build_no ]))
    return urllib.request.urlopen(url).read().decode('utf-8')

def parse_jenkins(json_data):
    test_states = {}
    for suite in json.loads(json_data)['suites']:
        for case in suite['cases']:
            test_states[case['className']+'/'+case['name']] = state_renaming[case['status']]
    return test_states

old_test_states = parse_jenkins(get_test_results(build_number_old))
new_test_states = parse_jenkins(get_test_results(build_number_new))

transitions = defaultdict(list)
for test_name in old_test_states.keys() | new_test_states.keys():
    old_state = old_test_states.get(test_name, 'Missing')
    new_state = new_test_states.get(test_name, 'Missing')
    transitions[(old_state, new_state)].append(test_name)

print('Summary:')
for (old_state, new_state), test_names in sorted(transitions.items()):
    if old_state != new_state:
        print('  - {0} -> {1}: {2} tests'.format(old_state, new_state, len(test_names)))

for (old_state, new_state), test_names in sorted(transitions.items()):
    if old_state != new_state:
        print('\n{0} -> {1}:'.format(old_state, new_state))
        for n in sorted(test_names):
            print('  - {0}'.format(n))
