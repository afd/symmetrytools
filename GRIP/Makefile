#################################################
JAVA_FILES = $(shell /usr/bin/find src -name *.java)
CLASS_FILES = $(JAVA_FILES:%.java=%.class)
DATA_FILES = $(shell /usr/bin/find src -name *.dat)

COMPILED_CLASS_FILES = $(shell /usr/bin/find src -name *.class | sed s/\\$$/\\o052/)

# 

default:
	echo "Please specify 'classes' or 'jars'"

classes: $(CLASS_FILES)

jars: GRIP.jar

GRIP.jar: $(CLASS_FILES)
	jar cmf manifest.txt $@ $(COMPILED_CLASS_FILES) $(DATA_FILES) && echo "GRIP.jar built successfully."

%.class: %.java
	javac $<

clean:
	@rm -f $(COMPILED_CLASS_FILES) GRIP.jar

#################################################
