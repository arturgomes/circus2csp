
#
# for j in 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20
# do
#   for i in "CTOC" "CTOCPre" "D241" "D241Inv" "D241Pre" "D241InvPre"
#   do
#     # touch tc.$i.$j.csp
#     file='tc.'$i'.'$j'.csp'
#     touch $file
#     cat tc.csp > $file
#     echo "MAXVAL = $j">>  $file
#     if [ $i = "CTOC" ]
#     then
#         echo "assert CTOC(b_RAN1) :[deadlock free [FD]]">>  $file
#     elif [ $i = "CTOCPre" ]
#     then
#         echo "assert CTOCPre(b_RAN1) :[deadlock free [FD]]">>  $file
#     else
#         echo "assert $i :[deadlock free [FD]]">>  $file
#     fi
#
#   done
# done
TIMEFORMAT=%R
for j in 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20
do
  for i in "CTOC" "CTOCPre" "D241" "D241Inv" "D241Pre" "D241InvPre"
  do
  file='tc.'$i'.'$j'.csp'
  # STARTTIME=`date +%s.%N`
  echo $i'-'$j
  time refines -q $file | grep -P 'States|real' | tee results.txt
  # End timestamp
  # ENDTIME=`date +%s.%N`
  # Convert nanoseconds to milliseconds
  # crudely by taking first 3 decimal places
  # TIMEDIFF=`echo "$ENDTIME - $STARTTIME" | bc | awk -F"." '{print $1"."substr($2,1,3)}'`
  # echo "$i  $j  $TIMEDIFF"
  done
done
