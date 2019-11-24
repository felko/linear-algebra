check:
	for f in src/**/*.agda ; do agda --library=linear-algebra $$f ; done

clean:
	rm src/**/*.agdai
