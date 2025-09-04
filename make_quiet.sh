#!/bin/bash
# Filename: make_fail_only.sh
# Usage: ./make_fail_only.sh [make arguments]

# Temporary log file
LOGFILE=$(mktemp /tmp/make_log.XXXXXX)

# Run make with all arguments, save stdout and stderr
make "$@" > "$LOGFILE" 2>&1

# Print only lines containing "FAIL"
grep --color=always "FAIL" "$LOGFILE"

# Exit with the same status as make
exit $?

