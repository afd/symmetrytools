echo off

set VERSION=2.2.4

set RELEASE=TopSPIN_%VERSION%

make clean

make jars

rm -rf %RELEASE%

rm -f %RELEASE%.tgz

mkdir %RELEASE%

mkdir %RELEASE%\documentation

mkdir %RELEASE%\documentation\papers
cp documentation\papers\FM2005.pdf %RELEASE%\documentation\papers\FM2005.pdf
cp documentation\papers\FM2006.pdf %RELEASE%\documentation\papers\FM2006.pdf
cp documentation\papers\AMAST2006.pdf %RELEASE%\documentation\papers\AMAST2006.pdf

mkdir %RELEASE%\documentation\thesis
cp documentation\thesis\DonaldsonThesis.pdf %RELEASE%\documentation\thesis\DonaldsonThesis.pdf

mkdir %RELEASE%\documentation\manual
cp documentation\manual\manual.pdf %RELEASE%\documentation\manual\TopSPIN_%VERSION%_manual.pdf

mkdir %RELEASE%\saucy
cp saucy/LICENSE %RELEASE%/saucy/LICENSE
cp saucy/Makefile %RELEASE%/saucy/Makefile
cp saucy/README %RELEASE%/saucy/README
cp saucy/main.c %RELEASE%/saucy/main.c
cp saucy/saucy.c %RELEASE%/saucy/saucy.c
cp saucy/saucy.h %RELEASE%/saucy/saucy.h
cp saucy/saucyio.c %RELEASE%/saucy/saucyio.c

mkdir %RELEASE%\Common
cp Common\Classify.gap %RELEASE%\Common\Classify.gap
cp Common\Enumerate.gap %RELEASE%\Common\Enumerate.gap
cp Common\LocalSearch.gap %RELEASE%\Common\LocalSearch.gap
cp Common\OutputPerm.gap %RELEASE%\Common\OutputPerm.gap
cp Common\StabilizerChainCosets.gap %RELEASE%\Common\StabilizerChainCosets.gap
cp Common\WorkspaceGenerator.gap %RELEASE%\Common\WorkspaceGenerator.gap
cp Common\Disjoint.gap %RELEASE%\Common\Disjoint.gap
cp Common\EnumerationStrategies.gap %RELEASE%\Common\EnumerationStrategies.gap
cp Common\Minimising.gap %RELEASE%\Common\Minimising.gap
cp Common\PermutationToTranspositions.gap %RELEASE%\Common\PermutationToTranspositions.gap
cp Common\Verify.gap %RELEASE%\Common\Verify.gap
cp Common\Wreath.gap %RELEASE%\Common\Wreath.gap
cp Common\groupBasic.c %RELEASE%\Common\groupBasic.c
cp Common\groupTranspositions.c %RELEASE%\Common\groupTranspositions.c
cp Common\parallel_symmetry_cell_ppu.c %RELEASE%\Common\parallel_symmetry_cell_ppu.c
cp Common\parallel_symmetry_cell_spu.c %RELEASE%\Common\parallel_symmetry_cell_spu.c
cp Common\parallel_symmetry_pthreads.c %RELEASE%\Common\parallel_symmetry_pthreads.c
cp Common\groupBasic.h %RELEASE%\Common\groupBasic.h
cp Common\groupTranspositions.h %RELEASE%\Common\groupTranspositions.h
cp Common\parallel_symmetry_cell_ppu.h %RELEASE%\Common\parallel_symmetry_cell_ppu.h
cp Common\parallel_symmetry_cell_spu.h %RELEASE%\Common\parallel_symmetry_cell_spu.h
cp Common\parallel_symmetry_pthreads.h %RELEASE%\Common\parallel_symmetry_pthreads.h
cp Common\segment.h %RELEASE%\Common\segment.h

mkdir %RELEASE%\examples
cp examples\loadbalancer.p %RELEASE%\examples\loadbalancer.p

cp TopSPIN.jar %RELEASE%\TopSPIN_%VERSION%.jar

cp releasenotes.txt %RELEASE%\releasenotes.txt

tar -cvf %RELEASE%.tar %RELEASE%
gzip %RELEASE%.tar
mv %RELEASE%.tar.gz %RELEASE%.tgz

pause

