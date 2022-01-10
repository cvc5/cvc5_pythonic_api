#!/usr/bin/env zsh

set -e

for p in $(ls ./test/pgms/)
do
    pgm="./test/pgms/$p"
    out="./test/pgm_outputs/$p.out"
    if [[ ! ( -a $out ) ]]
    then
        python $pgm > out
        cat $pgm
        echo "$pgm (above) gave the following output:"
        cat out
        read -q "REPLY?Accept this output? [y/N] "
        case ${REPLY:l} in
            y|Y)
                mv out $out
                ;;
            *)
                rm out
                exit 2
                ;;
        esac
    fi
done

