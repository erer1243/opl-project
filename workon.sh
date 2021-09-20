#!/bin/sh
set -e

node_count() {
  bspc query --nodes | wc -l
}

NODES="$(node_count)"
if [ $(hostname) = small ]; then
	CHROMIUM=chromium
	EDITCMD="alacritty -e vim high-level/hl.hs & disown"
else
	CHROMIUM=chromium-freeworld
	EDITCMD="sublime_text -a ."
fi

bspc node --presel-dir north --presel-ratio 0.8
$CHROMIUM --new-window "https://jeapostrophe.github.io/courses/2021/fall/301/course/" >/dev/null 2>&1 &
disown

while [ $(node_count) = $NODES ]; do 
	sleep 0.01
done

bspc node --presel-dir west --presel-ratio 0.6
eval "$EDITCMD"
