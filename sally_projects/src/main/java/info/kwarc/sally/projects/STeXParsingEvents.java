package info.kwarc.sally.projects;

public interface STeXParsingEvents {
	void beginModule(String fileURL, String moduleID, int offset);
	void symbolDec(String symbolId, int offset);
	void importModule(String theory, String symbol, int offset);
}
