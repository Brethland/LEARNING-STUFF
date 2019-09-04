use 5.20.1;
use strict;

# Nothing 01

my $foo = 1;
my $foo = \$foo;
say $$foo;

my $dp = <STDIN>;
my @ls = split(' ',$dp,2);
my (@tim,@f);
for(my $i = 1; $i <= $ls[0]; $i++){
    $tim[$i] = <STDIN>;
}
