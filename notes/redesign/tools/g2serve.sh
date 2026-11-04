#!/bin/bash
# g2serve.sh: gen2 servers for the prover swarm, OUTSIDE heavy.sh's 3 gate slots.
# Installed as ~/lead/g2serve.sh (a symlink to reports/redesign/tools/g2serve.sh, versioned there).
#
# Each server is a systemd user service `g2pool-<port>` in the slice g2pool.slice: its own memory
# cap (MemoryMax, no swap: a server over its cap is killed alone), nice, and the slice caps all
# servers together (so gates keep their memory). One server per entry file (a lane's proof file);
# many agents share it: each `gen2.ts ask --file <their worktree copy>` sends its own text (see
# gen2.ts's header, SHARED SERVERS). The registry (one <port>.json per server) lives on the Windows
# disk, so that clients in Windows and in WSL find a file's server: /mnt/c/Users/mathe/.g2pool/.
#
#   g2serve.sh start WT FILE [--mem 3G] [--port N] [--nice 10] [--gen2 PATH] [--replicas K] [-- <gen2 serve options>]
#       WT: the worktree whose imports the server loads (C:\... or /mnt/c/...; use a clean checkout
#       of feature/redesign, e.g. bb-wt/pool); FILE: the entry, under src/ (Compiler/Machine/x.bend).
#       Prints the port(s) once the book is loaded (exit 0), or the log's tail (exit 1). A server for
#       the same WT and FILE already running: prints its port. --gen2: the gen2.ts to run (default
#       WT's own src/Shared/scripts/gen2.ts). --replicas K: K servers of FILE (K x the memory; each
#       client worktree always asks the same replica): for a file that many agents share at once.
#   g2serve.sh stop PORT|FILE|all       stop servers (by port, by entry FILE, or all)
#   g2serve.sh restart PORT|FILE        stop and start again with the same WT, FILE and options
#   g2serve.sh list                     port, state, memory now/peak, entry, worktree
#   g2serve.sh log PORT                 the server's log (gen2's stderr: loads, reloads, timings)
#   g2serve.sh hold                     keeps WSL up while servers run (the distro stops when no
#                                       wsl.exe is attached, and every server with it): waits up to 10
#                                       min for a first server, then blocks while any runs; one at a
#                                       time (a lock). WSL's interop is off, so start it FROM WINDOWS
#                                       (PowerShell; it outlives the shell that starts it):
#     Start-Process -WindowStyle Hidden wsl.exe -ArgumentList '-d','Ubuntu-24.04','-e','/home/math/lead/g2serve.sh','hold'
#                                       `start` warns when no holder runs.
#   env: G2POOL_SLICE_MAX (default 10G): all servers together; G2POOL_REG: the registry dir
export PATH=$HOME/.bun/bin:/usr/local/bin:/usr/bin:/bin
REG=${G2POOL_REG:-/mnt/c/Users/mathe/.g2pool}
LOGS=~/lead/g2pool-logs
SLICE_MAX=${G2POOL_SLICE_MAX:-10G}
mkdir -p "$REG" "$LOGS"
[ -e ~/.g2pool ] || ln -s "$REG" ~/.g2pool # gen2.ts ask finds the registry in ~/.g2pool
HOLD_LOCK=~/lead/locks/g2hold

wsl_path() { # C:\a\b or C:/a/b -> /mnt/c/a/b; others unchanged
  local p=${1//\\//}
  if [[ $p =~ ^([A-Za-z]):(/.*)?$ ]]; then echo "/mnt/${BASH_REMATCH[1],,}${BASH_REMATCH[2]}"; else echo "$p"; fi
}
field() { sed -n "s/.*\"$2\": *\"\\{0,1\\}\\([^\",}]*\\).*/\\1/p" "$1"; }
alive() { case $(systemctl --user show -p ActiveState --value "g2pool-$1.service" 2>/dev/null) in active|activating|reloading) return 0 ;; *) return 1 ;; esac; } # also while it restarts
prune() { for f in "$REG"/*.json; do [ -e "$f" ] || continue; p=$(basename "$f" .json); alive "$p" || rm -f "$f"; done; }
ports_of() { # PORT, FILE (entry under src/) or all -> ports
  prune
  for f in "$REG"/*.json; do
    [ -e "$f" ] || continue; p=$(basename "$f" .json)
    if [ "$1" = all ] || [ "$1" = "$p" ] || [ "$1" = "$(field "$f" file)" ]; then echo "$p"; fi
  done
}

hold() {
  exec 8> "$HOLD_LOCK"; flock -n 8 || { echo "g2serve: a holder already runs"; return 0; }
  for _ in $(seq 1 60); do [ -n "$(ports_of all)" ] && break; sleep 10; done
  while [ -n "$(ports_of all)" ]; do sleep 30; done
}
warn_holder() {
  ( exec 8> "$HOLD_LOCK"; flock -n 8 ) || return 0
  echo "g2serve: WARNING: no holder runs, so WSL may stop (and kill the servers) when no wsl.exe is attached. From Windows PowerShell:" >&2
  echo "  Start-Process -WindowStyle Hidden wsl.exe -ArgumentList '-d','Ubuntu-24.04','-e','/home/math/lead/g2serve.sh','hold'" >&2
}

start() {
  local wt file mem=3G port="" nice=10 g2="" rep=1 extra=()
  wt=$(wsl_path "$1"); file=$2; shift 2
  while [ $# -gt 0 ]; do
    case $1 in
      --mem) mem=$2; shift 2 ;;
      --port) port=$2; shift 2 ;;
      --nice) nice=$2; shift 2 ;;
      --gen2) g2=$(wsl_path "$2"); shift 2 ;;
      --replicas) local k=$2; shift 2
        for i in $(seq 2 "$k"); do start "$wt" "$file" --mem "$mem" --nice "$nice" ${g2:+--gen2 "$g2"} --replicas 1 --replica "$i" "$@" || return 1; done ;;
      --replica) rep=$2; shift 2 ;;
      --) shift; extra=("$@"); break ;;
      *) echo "g2serve: unknown option $1" >&2; return 2 ;;
    esac
  done
  [ -f "$wt/src/$file" ] || { echo "g2serve: no file $wt/src/$file" >&2; return 2; }
  g2=${g2:-$wt/src/Shared/scripts/gen2.ts}
  [ -f "$g2" ] || { echo "g2serve: no $g2" >&2; return 2; }
  [ -e "$(dirname "$g2")/../../../bend/bend2/bend.ts" ] || { echo "g2serve: the bend of $g2 is not linked to a bend checkout (ln -s .../bend-bootstrap/bend <worktree>/bend)" >&2; return 2; }
  prune
  for f in "$REG"/*.json; do
    [ -e "$f" ] || continue
    if [ "$(field "$f" file)" = "$file" ] && [ "$(field "$f" wt)" = "$wt" ] && [ "$(field "$f" replica)" = "$rep" ]; then basename "$f" .json; return 0; fi
  done
  if [ -z "$port" ]; then
    port=7400
    while [ -e "$REG/$port.json" ] || alive "$port" || ss -ltn "sport = :$port" | grep -q LISTEN; do port=$((port + 1)); done
  fi
  warn_holder
  local log=$LOGS/$port.log
  : > "$log"
  systemctl --user reset-failed "g2pool-$port.service" 2>/dev/null
  systemd-run --user -q --unit="g2pool-$port" --slice=g2pool.slice \
    -p MemoryMax="$mem" -p MemorySwapMax=0 -p Nice="$nice" -p Restart=on-failure -p RestartSec=5 -p WorkingDirectory="$wt/src" \
    -p StandardOutput="append:$log" -p StandardError="append:$log" \
    "$(command -v bun)" "$g2" serve "$file" --port "$port" "${extra[@]}" || return 1
  systemctl --user set-property --runtime g2pool.slice MemoryMax="$SLICE_MAX" MemorySwapMax=0 2>/dev/null
  local q=""; [ ${#extra[@]} -gt 0 ] && { q=$(printf '"%s",' "${extra[@]}"); q=${q%,}; }
  printf '{"port": %s, "replica": %s, "file": "%s", "wt": "%s", "gen2": "%s", "mem": "%s", "nice": %s, "extra": [%s], "started": "%s"}
'     "$port" "$rep" "$file" "$wt" "$g2" "$mem" "$nice" "$q" "$(date -Is)" > "$REG/$port.json"
  for _ in $(seq 1 300); do
    if grep -q "serving" "$log"; then echo "$port"; return 0; fi
    alive "$port" || break
    sleep 1
  done
  echo "g2serve: the server on $port did not start; its log:" >&2; tail -20 "$log" >&2
  systemctl --user stop "g2pool-$port.service" 2>/dev/null; rm -f "$REG/$port.json"
  return 1
}

stop() {
  local any=1
  for p in $(ports_of "$1"); do systemctl --user stop "g2pool-$p.service"; rm -f "$REG/$p.json"; echo "stopped $p"; any=0; done
  return $any
}

restart() {
  for p in $(ports_of "$1"); do
    local f=$REG/$p.json wt file mem nice g2 extra rp
    rp=$(field "$f" replica); wt=$(field "$f" wt); file=$(field "$f" file); mem=$(field "$f" mem); nice=$(field "$f" nice); g2=$(field "$f" gen2)
    extra=$(sed -n 's/.*"extra": \[\([^]]*\)\].*/\1/p' "$f" | tr -d '"' | tr ',' ' ')
    stop "$p" > /dev/null
    # shellcheck disable=SC2086
    start "$wt" "$file" --mem "$mem" --nice "$nice" --port "$p" ${g2:+--gen2 "$g2"} --replica "${rp:-1}" -- $extra
  done
}

list() {
  prune
  printf '%-6s %-9s %8s %8s  %s\n' PORT STATE MEM PEAK "ENTRY (WORKTREE)"
  for f in "$REG"/*.json; do
    [ -e "$f" ] || continue; p=$(basename "$f" .json)
    eval "$(systemctl --user show "g2pool-$p.service" -p ActiveState -p MemoryCurrent -p MemoryPeak | sed 's/=/="/; s/$/"/')"
    printf '%-6s %-9s %7sM %7sM  %s (%s)\n' "$p" "$ActiveState" $((${MemoryCurrent:-0} >> 20)) $((${MemoryPeak:-0} >> 20)) "$(field "$f" file)" "$(field "$f" wt)"
  done
  local s; s=$(systemctl --user show g2pool.slice -p MemoryCurrent -p MemoryMax | tr '\n' ' ')
  echo "slice g2pool: $s"
}

case $1 in
  start) shift; start "$@" ;;
  stop) stop "$2" ;;
  restart) restart "$2" ;;
  list) list ;;
  log) cat "$LOGS/$2.log" ;;
  hold) hold ;;
  *) sed -n '2,25p' "$0"; exit 2 ;;
esac
