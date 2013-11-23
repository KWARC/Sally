package info.kwarc.sally.sharejs;

import info.kwarc.sally.sharejs.text.TextOp;

public class TextSnapshot extends AbstractSnapshot{
	String snapshot;
	IDocManager docManager;
	
	private TextSnapshot(IDocManager docManager) {
		super();
		this.docManager = docManager;
	}

	private void setSnapshot(String snapshot) {
		this.snapshot = snapshot;
	}
	
	public String getSnapshot() {
		return snapshot;
	}

	public static TextSnapshot create(IDocManager docManager, String collection, String fileName, String content) {
		ISyncResult result = docManager.sendOp(collection, fileName, new DocumentCreateRequest().setData(content).setType(IDocManager.textType));
		Long version = result.getVersion() + 1;
		TextSnapshot snap = new TextSnapshot(docManager);
		snap.setCollection(collection).setFileName(fileName).setVersion(version);
		snap.setSnapshot(content);
		return snap;
	}
	
	public static TextSnapshot retrieveSnapshot(IDocManager docManager, String collection, String fileName) {
		TextSnapshot snap = new TextSnapshot(docManager);
		snap.setCollection(collection).setFileName(fileName);
		
		ISyncResult result = docManager.getSnapshot(collection, fileName, snap);
		snap.setVersion(result.getVersion());
		return snap;
	}	

	public void insertText(int offset, String text) {
		ISyncResult result= docManager.sendOp(getCollection(), getFileName(), new TextOp().setBaseVersion(getVersion()).addSkipOp(offset).addInsertOp(text));
		this.version = result.getVersion() + 1;
	}

	public void removeText(int offset, int len) {
		ISyncResult result= docManager.sendOp(getCollection(), getFileName(), new TextOp().setBaseVersion(getVersion()).addSkipOp(offset).addRemoveOp(len));
		this.version = result.getVersion() + 1;
	}

	public static void main(String[] args) {
		ShareJS sharejs = new ShareJS("http://localhost:7007");
		TextSnapshot u1 = TextSnapshot.create(sharejs, "test", "test.txt", "hi there");
		TextSnapshot u2 = TextSnapshot.retrieveSnapshot(sharejs, "test", "test.txt");
		
		u1.insertText(8, " everyone!");
		u2.insertText(9, "another one\n");
		
		sharejs.deleteFile("test", "test.txt");
	}

	@Override
	public void setSnapshot(String otType, String data) {
		if (!IDocManager.textType.equals(otType)) 
			return;
		
		setSnapshot(data);
	}
}
