package skinner.util;

public class Position {
    String path;
    String file;
    int startLine;
    int startColumn;
    int endLine;
    int endColumn;

    public Position(String path, String file, int startLine, int startColumn, int endLine, int endColumn) {
	this.path = path;
	this.file = file;
	this.startLine = startLine;
	this.startColumn = startColumn;
	this.endLine = endLine;
	this.endColumn = endColumn;
    }
}

