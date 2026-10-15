#!/usr/bin/env python3
"""mkin.py N OUT : N random numbers below 10^9, one per line."""
import sys, random
random.seed(7); n = int(sys.argv[1])
open(sys.argv[2], 'w').write(''.join('%d\n' % random.randint(0, 999999999) for _ in range(n)))
