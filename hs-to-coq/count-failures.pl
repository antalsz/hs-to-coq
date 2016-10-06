#!/usr/bin/perl -w
use strict;
use v5.10;

use List::Util qw(sum0 max);

my %failures = ();

{
  my $cur_comment = undef;
  while (<>) {
    $_ = $cur_comment.$_ if $cur_comment;
    $cur_comment = s/^\(\*(?!.+\*\)\n)(.*)\n/(*$1/ ? $_ : undef;
    tr/ / /s;
    ++$failures{$1} if /^\(\*.+failed: +(.+?) +unsupported.*\*\)$/;
  }
}

my @failures = ();
while (my ($reason, $count) = each %failures) {
  push @failures, [$count,$reason];
}
@failures = sort { $b->[0] <=> $a->[0] || $a->[1] cmp $b->[1] } @failures;

sub format_result(_;$) {
  my ($count, $reason) = ref($_[0]) eq 'ARRAY' ? @{$_[0]} : @_;
  return sprintf '%4d %s', $count, $reason;
}

my $total      = sum0(map { $_->[0] } @failures);
my @lines      = map format_result, @failures;
my $total_line = format_result $total, 'TOTAL';
my $rule       = '-' x max(map length, $total_line, @lines);

say foreach @lines, $rule, $total_line;
