#!/usr/bin/env python3
"""Run a command and write its CPU time and peak memory to a JSON file.

  timed_exec.py <stats.json> -- <command> [args...]

Used inside the sandbox, directly around the compiler, so the numbers are the compiler's own
(the sandbox and memory-cap wrappers do not pass resource usage up to their parent).
"""
import json, os, sys, time


def main():
    stats = sys.argv[1]
    cmd = sys.argv[sys.argv.index('--') + 1:]
    t0 = time.time()
    pid = os.fork()
    if pid == 0:
        try:
            os.execvp(cmd[0], cmd)
        finally:
            os._exit(127)
    _, status, ru = os.wait4(pid, 0)
    rc = os.waitstatus_to_exitcode(status)
    with open(stats, 'w') as fh:
        json.dump({'rc': rc, 'user_s': ru.ru_utime, 'sys_s': ru.ru_stime, 'wall_s': time.time() - t0,
                   'max_rss_mb': ru.ru_maxrss / 1024.0}, fh)
    sys.exit(rc if rc >= 0 else 128 - rc)


if __name__ == '__main__':
    main()
