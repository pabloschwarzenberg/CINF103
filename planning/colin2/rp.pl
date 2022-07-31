#!/usr/bin/perl -w
use File::Basename;

if ((scalar @ARGV) != 5) {
	print "Usage: rp.pl <domain> <problem> <rplan> <rplan_actions> <timing>\n";
	exit(1);
}

$dir = dirname(__FILE__);
$dom = shift @ARGV;
$prob = shift @ARGV;
$rp = shift @ARGV;
$rp_actions = shift @ARGV;
$timing = shift @ARGV;

if (!(-e $dom)) {
	print "Domain file $dom not found\n";
	exit(1);
}

if (!(-e $prob)) {
  print "Problem file $prob not found\n";
  exit(1);
}

exec("$dir/bin/colin-clp", "-x", "$rp", "$rp_actions", "-y", "$timing", "$dom", "$prob")
