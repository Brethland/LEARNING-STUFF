use 5.20.1;
use strict;

# Three easiest ways of inner sort.

my $n = <STDIN>;
my @array = split(/ /,<STDIN>),my @inst = my @array, my @bubble = my @array, my @chose = my @array;
my $ins = localtime();
for(my $i = 0; $i < $n; $i++) {
    my $j;
    for ($j = $i - 1; $j >= 0&&$inst[$j] > $inst[$i]; $j++) {
        $inst[$j + 1] = $inst[$j];
    }
    $inst[$j] = $inst[$i];
}
say localtime() - $ins;
$ins = localtime();
for(my $i = 0; $i < $n - 1; $i ++) {
    for(my $j = $i + 1; $j < $n; $j++) {
        if($chose[$j] < $chose[$i]) {
            $chose[$i] ^= $chose[$j];
            $chose[$j] ^= $chose[$i];
            $chose[$i] ^= $chose[$j];
        }
    }
}
say localtime() - $ins;
$ins = localtime();
for(my $i = $n - 1; $i >= 0; $i --) {
    for(my $j = $i; $j > 0; $j --) {
        if($bubble[$j] < $bubble[$j - 1]){
            $bubble[$j] ^= $bubble[$j-1];
            $bubble[$j - 1] ^= $bubble[$j];
            $bubble[$j] ^= $bubble[$j - 1];
        }
    }
}
say localtime() - $ins;