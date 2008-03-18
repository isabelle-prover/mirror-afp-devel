#!/usr/bin/perl
#
# $Id: report.pl,v 1.4 2008-03-18 07:25:55 lsf37 Exp $
# Author: Gerwin Klein, NICTA
#
# Parses log file and generates report of entry status.
# Prints out diff to last report.
#

if ($#ARGV!=1) {
  print "usage: report.pl <logfile> <report-file>\n";
  exit 1;
}

$logfile=$ARGV[0];
$report=$ARGV[1];

$FAIL="FAIL";
$OK="ok";

# read log file
open (IN,$logfile) || die "could not open [$logfile]";
@lines = <IN>;
close IN;

# parse log file
for $i ( 0 .. $#lines) {
  $_ = $lines[$i];
  if ( /^Testing \[([^\]]+)\]/ ) {
    $tests{$1} = 1;
  }
  if ( /The following tests failed/ ) {
    foreach $f (split (/[ \n]/,$lines[$i+1])) {
      $fail{$f} = 1;
    }
  }
}

# read and parse old report
open (IN,$report);
while (<IN>) {
  chop;
  ($name, $f) = split /[:]/;
  $old_tests{$name} = 1;
  $old_fail{$name} = ($f =~ /$FAIL/);
}
close IN;

# save old report
rename ($report, $report.".old");

# write new report
open (OUT,">$report") || die "could not open [$report] for writing.";
foreach $t (keys tests) {
  $status = $fail{$t} ? $FAIL : $OK;
  print OUT "$t: $status\n";
}
close OUT;

# output diff
foreach $t (keys old_tests) {
  $old_status = $old_fail{$t} ? $FAIL : $OK;
  $new_status = $fail{$t} ? $FAIL : $OK;
  if (!$tests{$t}) {
    print "[$t] was removed. Last status was $old_status.\n";
  }
  elsif ($old_fail{$t} != $fail{$t}) {
    print "[$t] changed from $old_status to $new_status.\n";
  }
  elsif ($fail{$t}) {
    print "[$t] is still on $new_status.\n";
  }
}

foreach $t (keys tests) {
  if (!$old_tests{$t}) {
    $new_status = $fail{$t} ? $FAIL : $OK;
    print "[$t] is new. Status is $new_status.\n";
  }
}
