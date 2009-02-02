

open FILE, "src/promela/node/Node.java" or die $!;

my @lines = <FILE>;

close(FILE);

open FILE, "Node.java.patch" or die $!;

my @patch = <FILE>;

close(FILE);

open FILE, ">src/promela/node/Node.java" or die $!; 

foreach(@lines)
{
    if($_ =~ m/cloneList/) {
	last;
    } else {
	print FILE $_;
    }
}

foreach(@patch)
{
    print FILE $_;
}

print FILE "}\n";

close(FILE);

