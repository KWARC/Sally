package info.kwarc.sally.spreadsheet;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyService;

import java.util.HashMap;

import org.apache.commons.codec.binary.Base64;
import org.eclipse.jetty.util.ajax.JSON;

import sally.SemanticData;
import sally.SpreadsheetModel;
import sally.WhoAmI;
import sally.WhoAmI.ClientType;
import sally.WhoAmI.DocType;

import com.google.protobuf.InvalidProtocolBufferException;
import com.hp.hpl.jena.ontology.OntDocumentManager;
import com.hp.hpl.jena.ontology.OntModel;
import com.hp.hpl.jena.rdf.model.ModelFactory;

public class WorksheetFactory {

	OntModel loadOntology(String path) {
		OntModel m = ModelFactory.createOntologyModel();
		m.read(getClass().getResourceAsStream(path), null);
		return m;
	}
	
	OntModel csm, asm;
	
	public WorksheetFactory() {
		OntDocumentManager doc = OntDocumentManager.getInstance();
		csm = loadOntology("/csm_rdf.owl");
		doc.addModel("http://www.kwarc.info/sally/csm", csm);
		asm = loadOntology("/asm_rdf.owl");
	}
	
	@SallyService(channel="/service/alex/register")
	public void worksheets(WhoAmI whoami, SallyActionAcceptor acceptor, SallyContext context) {
		if (whoami.getClientType() == ClientType.Alex && whoami.getDocumentType() == DocType.Spreadsheet) {
			acceptor.acceptResult(sally.Init.newBuilder().build());
		}
	}
	
	@SallyService(channel="/service/sissi/loadSemanticData")
	public void createWorksheet(SemanticData msg, SallyActionAcceptor acceptor, SallyContext context) {
		WorksheetDocument doc = new WorksheetDocument(msg.getFileName());
		
		if (msg.hasData()) {
			HashMap<String, Object> map = new HashMap<String, Object>();
			map = (HashMap<String, Object>) JSON.parse(msg.getData());
			String base64Map = (String) map.get("interpretationMap");
			byte[] res = Base64.decodeBase64(base64Map);
			try {
				SpreadsheetModel rr = SpreadsheetModel.parseFrom(res);
				doc.setSemanticData(rr);
			} catch (InvalidProtocolBufferException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		context.getCurrentInteraction().registerServices(doc);
	}
	
}
