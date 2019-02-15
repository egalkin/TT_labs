HC=ghc
#HC=ghc
SOURCES=src/Main.hs src/Grammar.hs src/Lexer.hs src/Parser.hs src/Types.hs
PACKAGE=hw1.zip

.PHONY: all run clean

all: parenthesesPutter

run: parenthesesPutter
	./parenthesesPutter

clean:
	rm -rf src/*.o src/*.hi
	rm -f parenthesesPutter

parenthesesPutter: $(SOURCES)
	$(HC) -i./src -tmpdir . ./src/Main.hs -o parenthesesPutter
