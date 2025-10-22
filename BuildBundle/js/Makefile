
# Define the default goal to be 'all'
all: build_bundle

# Define the 'build_bundle' target
build_bundle:
	./esbuild --bundle helpers.js --outfile=bundle.js --format=iife --global-name=Bundle

# .PHONY is used to tell make that a target is not a file to be created.
# This ensures the command always runs, even if a file named 'all' or 'build_bundle' exists.
.PHONY: all build_bundle
