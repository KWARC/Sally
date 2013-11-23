package info.kwarc.sally.jedit;

import info.kwarc.sally.sharejs.AbstractSnapshot;
import info.kwarc.sally.sharejs.IDocManager;
import info.kwarc.sally.sharejs.IDocumentOp;
import info.kwarc.sally.sharejs.ISyncResult;

public class LocalDoc implements IDocManager{

	
	
	@Override
	public boolean existFile(String collection, String document) {
		return false;
	}

	@Override
	public void deleteFile(String collection, String document) {

	}

	@Override
	public ISyncResult createDoc(String collection, String document,
			String docType, String content) {
		return null;
	}

	@Override
	public ISyncResult getSnapshot(String collection, String document,
			AbstractSnapshot snapshot) {
		return null;
	}

	@Override
	public ISyncResult sendOp(String collection, String document, IDocumentOp op) {
		return null;
	}

}
