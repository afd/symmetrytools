set VERSION=2.1

rm -rf release

mkdir release

mkdir release\documentation

mkdir release\documentation\papers

mkdir release\documentation\thesis

mkdir release\documentation\manual
cp documentation\manual\manual.pdf release\documentation\manual\TopSPIN_%VERSION%_manual.pdf

mkdir release\saucy
cp saucy/LICENSE release/saucy/LICENSE
cp saucy/Makefile release/saucy/Makefile
cp saucy/README release/saucy/README
cp saucy/main.c release/saucy/main.c
cp saucy/saucy.c release/saucy/saucy.c
cp saucy/saucy.h release/saucy/saucy.h
cp saucy/saucyio.c release/saucy/saucyio.c

mkdir release\Common
cp Common\Classify.gap release\Common\Classify.gap
cp Common\Enumerate.gap release\Common\Enumerate.gap
cp Common\LocalSearch.gap release\Common\LocalSearch.gap
cp Common\OutputPerm.gap release\Common\OutputPerm.gap
cp Common\StabilizerChainCosets.gap release\Common\StabilizerChainCosets.gap
cp Common\WorkspaceGenerator.gap release\Common\WorkspaceGenerator.gap
cp Common\Disjoint.gap release\Common\Disjoint.gap
cp Common\EnumerationStrategies.gap release\Common\EnumerationStrategies.gap
cp Common\Minimising.gap release\Common\Minimising.gap
cp Common\PermutationToTranspositions.gap release\Common\PermutationToTranspositions.gap
cp Common\Verify.gap release\Common\Verify.gap
cp Common\Wreath.gap release\Common\Wreath.gap
cp Common\groupBasic.c release\Common\groupBasic.c
cp Common\groupTranspositions.c release\Common\groupTranspositions.c
cp Common\parallel_symmetry_cell_ppu.c release\Common\parallel_symmetry_cell_ppu.c
cp Common\parallel_symmetry_cell_spu.c release\Common\parallel_symmetry_cell_spu.c
cp Common\parallel_symmetry_pthreads.c release\Common\parallel_symmetry_pthreads.c
cp Common\groupBasic.h release\Common\groupBasic.h
cp Common\groupTranspositions.h release\Common\groupTranspositions.h
cp Common\parallel_symmetry_cell_ppu.h release\Common\parallel_symmetry_cell_ppu.h
cp Common\parallel_symmetry_cell_spu.h release\Common\parallel_symmetry_cell_spu.h
cp Common\parallel_symmetry_pthreads.h release\Common\parallel_symmetry_pthreads.h
cp Common\segment.h release\Common\segment.h

mkdir release\examples
cp examples\loadbalancer.p release\examples\loadbalancer.p

cp TopSPIN.jar release\TopSPIN_%VERSION%.jar

pause