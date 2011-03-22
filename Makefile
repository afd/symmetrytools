#################################################
JAVA_FILES = $(shell /usr/bin/find src -name *.java)
CLASS_FILES = $(JAVA_FILES:%.java=%.class)
DATA_FILES = $(shell /usr/bin/find src -name *.dat)

COMPILED_CLASS_FILES = $(shell /usr/bin/find src -name *.class | sed s/\\$$/\\o052/)

# 

default:
	echo "Please specify 'classes' or 'jars'"

classes: $(CLASS_FILES)

jars: TopSPIN.jar TopSPINTests.jar LazySpinAnalysis.jar

TopSPIN.jar: $(CLASS_FILES)
	jar cmf manifest.txt $@ $(COMPILED_CLASS_FILES) $(DATA_FILES) && echo "TopSPIN.jar built successfully."

TopSPINTests.jar: $(CLASS_FILES)
	jar cmf tests_manifest.txt $@ $(COMPILED_CLASS_FILES) $(DATA_FILES) && echo "TopSPINTests.jar built successfully."

LazySpinAnalysis.jar: $(CLASS_FILES)
	jar cmf lazyspin_manifest.txt $@ $(COMPILED_CLASS_FILES) $(DATA_FILES) && echo "LazySpinAnalysis.jar built successfully."

%.class: %.java
	javac $<

clean:
	@rm -f $(COMPILED_CLASS_FILES) TopSPIN.jar TopSPINTests.jar

#################################################
