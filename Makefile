.PHONY: all clean checks

all: checks

checks:
	python3 ../../checks/genchecks.py
	$(MAKE) -C checks

clean:
	rm -rf ./checks
	echo $?

