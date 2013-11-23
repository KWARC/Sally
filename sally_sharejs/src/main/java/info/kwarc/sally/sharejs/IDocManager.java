package info.kwarc.sally.sharejs;

public interface IDocManager {

	public static final String textType = "http://sharejs.org/types/textv1";
	public static final String jsonType = "http://sharejs.org/types/JSONv0";

	public abstract boolean existFile(String collection, String document);

	public abstract void deleteFile(String collection, String document);

	public ISyncResult createDoc(String collection, String document, String docType, String content);
	public ISyncResult getSnapshot(String collection, String document, AbstractSnapshot snapshot);
	public ISyncResult sendOp(String collection, String document, IDocumentOp op);
}