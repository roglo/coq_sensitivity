# usage: ./def-nb-use.sh *.v
#    the command select-def.sh must have been run before;
#    returns the list of all theorems and definitions together with
#    the number of their occurences, sorted by increasing number

for i in $(cat def.txt); do grep -w $i $@ | grep -v Arguments | egrep -v '^[^:]*:\(\*' |  echo "$(wc -l) $i"; done | LC_ALL=C sort -n
