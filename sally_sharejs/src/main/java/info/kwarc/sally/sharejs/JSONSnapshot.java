package info.kwarc.sally.sharejs;

import info.kwarc.sally.sharejs.models.SpreadsheetModel;
import info.kwarc.sally.sharejs.models.SpreadsheetModel.Cell;
import info.kwarc.sally.sharejs.models.SpreadsheetModel.ChangeListener;

import java.io.IOException;
import java.util.ArrayList;

import com.fasterxml.jackson.databind.ObjectMapper;

public class JSONSnapshot extends AbstractSnapshot {
	IDocManager sharejs;
	
	String snapshot;
	
	public JSONSnapshot(IDocManager sharejs) {
		super();
		this.sharejs = sharejs;
	}
	
	private void setSnapshot(String snapshot) {
		this.snapshot = snapshot;
	}
	
	public String getSnapshot() {
		return snapshot;
	}
	
	public static JSONSnapshot retrieveSnapshot(IDocManager docManager, String collection, String fileName) {
		JSONSnapshot snap = new JSONSnapshot(docManager);
		snap.setCollection(collection).setFileName(fileName);
		
		ISyncResult result = docManager.getSnapshot(collection, fileName, snap);
		if (result != null)
			snap.setVersion(result.getVersion());
		return snap;
	}
	
	public static JSONSnapshot create(IDocManager docManager, String collection, String fileName, String content) {
		ISyncResult result = docManager.sendOp(collection, fileName, new DocumentCreateRequest().setData(content).setType(IDocManager.jsonType));
		Long version = result.getVersion() + 1;
		JSONSnapshot snap = new JSONSnapshot(docManager);
		snap.setCollection(collection).setFileName(fileName).setVersion(version);
		snap.setSnapshot(content);
		return snap;
	}
	
	public static void main(String[] args) throws IOException {
		ShareJS shareJS = new ShareJS("http://localhost:7007");
		String collection = "jedit";
		String file = "test.xls";
		ObjectMapper mapper = new ObjectMapper(); // create once, reuse
		
		if (!shareJS.existFile(collection, file)) { 
			SpreadsheetModel q = new SpreadsheetModel();
			q.addSheet("Vendor A")
				.setContent(1, 1, new Cell().setValue("11"))
				.setContent(1, 2, new Cell().setValue("12").setFormula("=12"));
			String json = mapper.writeValueAsString(q);
			JSONSnapshot.create(shareJS, collection, file, json);			
		} else {
			JSONSnapshot snap = JSONSnapshot.retrieveSnapshot(shareJS, collection, file);
			SpreadsheetModel model = mapper.readValue(snap.getSnapshot(), SpreadsheetModel.class);
			System.out.println(snap.getSnapshot());
			SpreadsheetModel.ChangeAcceptor acc = new SpreadsheetModel.ChangeAcceptor() {
				@Override
				public void acceptOp(String op) {
					System.out.println(op);
				}				
			};

			model.setChangeListener(new ChangeListener(acc, new ArrayList<String>()));
			
			model.addSheet("blah");
			System.out.println(model.getSheets().size());
		}
		
	}

	@Override
	public void setSnapshot(String otType, String data) {
		if (!IDocManager.jsonType.equals(otType)) 
			return;
		
		this.snapshot = data;
	}
}