CXX = g++
CXXFLAGS = -pthread -std=c++17
LDFLAGS = -pthread
SOURCE = $(wildcard *.cpp)
OBJECTS = $(SOURCE:.cpp=.o)
TARGET = philosophers

default: $(TARGET)

%.o: %.cpp
	$(CXX) $(CXXFLAGS) -c -o $@ $< $(LDFLAGS)

philosophers: $(OBJECTS)
	$(CXX) $(CXXFLAGS) $< -o $@ $(LDFLAGS)

clean:
	rm -f $(OBJECTS) $(TARGET)
