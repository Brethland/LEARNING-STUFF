use 5.20.1;
use strict;

# A codeforces problem written in Perl.

my $n = <STDIN>,my $m = <STDIN>;
my @dig,my $it = 0,my $pos,my $i = 0,my $flag = 1;
while($n) {
    @dig[$it++] = $n % 10;
    $n = int($n/10);
}
@dig = sort @dig;
for (my $j = 0; ($j < $it) && ($flag); $j++){
    if($dig[$j] != 0){
        $pos = $j;
        $flag = 0;
    }
}
my $ans = $dig[$pos] * (10 ** --$it);
while($it) {
    $ans += $dig[$i] * (10 ** --$it) unless ($i == $pos);
    $i++;
}
say 'OK' if ($ans == $m);
say 'WRONG_ANSWER' unless ($ans == $m);