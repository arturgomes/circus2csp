# a single file that both generates files for testing and also makes the tests.

# This generates files for testing
for j in 10 20 30
do
# those are my processes
  for i in "P1" "P2" "P3"
  do
    # touch tc.$i.$j.csp
    file='tc.'$i'.'$j'.csp'
    touch $file
# this is my source CSP code
    cat tc.csp > $file
# this is what I want to vary in my experiments
    echo "MAXVAL = $j">>  $file
# and the conditional below write different assertions depending on my $i variable
    if [ $i = "P1" ]
    then
        echo "assert P1 :[deadlock free [FD]]">>  $file
    elif [ $i = "P2" ]
    then
        echo "assert P2 :[deadlock free [FD]]">>  $file
    else
        echo "assert $i :[deadlock free [FD]]">>  $file
    fi

  done
done

# # This makes the tests themselves and writes on a file the results.
TIMEFORMAT=%R
for j in 10 20 30 # what are the values (like nat numbers) you want to evaluate
do
  for i in "CTOC" "CTOCPre" "D241" "D241Inv" "D241Pre" "D241InvPre"
  do
  file='tc.'$i'.'$j'.csp'
  # just print what is being tested
  echo $i'-'$j
  # this damm line gets the real time for execution and the number of states visited.
  time refines -q $file | grep -P 'States|real'

  done
done
