CC=gcc
CFLAGS=-Iincludes -Wall -Wextra -Wformat -std=c99 -pedantic
SRCDIR=src
OBJDIR=target
OBJS=$(OBJDIR)/core/scanner.o \
	$(OBJDIR)/core/token.o \
	$(OBJDIR)/utils.o
TESTS=test/core/token_test.c \
	  test/core/scanner_test.c

$(OBJDIR)/%.o : $(SRCDIR)/%.c includes/%.h
	$(CC) $(CFLAGS) -c $< -o $@

# make dir to store the .o files, if it doesn't already exist
makeTargetDir:
	mkdir -p $(OBJDIR)
	mkdir -p $(OBJDIR)/core

compile: makeTargetDir $(OBJS)

# create test result dir, if needed
makeTestDir:
	mkdir -p test-results

# compile AND run the unit tests
test: compile makeTestDir
	$(CC) $(CFLAGS) test/runner.c test/test.c $(TESTS) $(OBJS) -o tests
	./tests

# remove everything, if they exist
clean:
	-rm -f $(OBJDIR)/*.o
	-rm -f $(OBJDIR)/*/*.o
	-rm -f tests

# create the doxygen HTML documentation
docs:
	mkdir -p doc
	doxygen Doxyfile
