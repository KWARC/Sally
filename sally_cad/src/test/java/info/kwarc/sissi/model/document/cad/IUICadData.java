package info.kwarc.sissi.model.document.cad;
import info.kwarc.sissi.model.document.cad.ACMInterface;
import sally.CADNode;
import sally.Parameter;

public class IUICadData {

	public IUICadData() {
	}

	public void run() {
		CADNode.Builder root = CADNode.newBuilder().setId("pipe_end");
		
		String ht = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexbolt.omdoc?ISOhexbolt?ISOhexthread";
		String ct = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/components.omdoc?component?component";
		String boltIM = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexbolt.omdoc?ISOhexbolt?ISOhexbolt";
		
		root.addChildren(CADNode.newBuilder().setId("bolt1")
				.setImUri(boltIM)
				.addParameters(Parameter.newBuilder().setKey(ht).setValue("M15").build())
				.addParameters(Parameter.newBuilder().setKey(ct).setValue("bolt").build()).build());
		
		root.addChildren(CADNode.newBuilder().setId("bolt2")
				.setImUri(boltIM)
				.addParameters(Parameter.newBuilder().setKey(ht).setValue("M15").build())
				.addParameters(Parameter.newBuilder().setKey(ct).setValue("bolt").build()).build());

		root.addChildren(CADNode.newBuilder().setId("bolt3")
				.setImUri(boltIM)
				.addParameters(Parameter.newBuilder().setKey(ht).setValue("M15").build())
				.addParameters(Parameter.newBuilder().setKey(ct).setValue("bolt").build()).build());
		
		root.addChildren(CADNode.newBuilder().setId("bolt4")
				.setImUri(boltIM)
				.addParameters(Parameter.newBuilder().setKey(ht).setValue("M15").build())
				.addParameters(Parameter.newBuilder().setKey(ct).setValue("bolt").build()).build());
		
		ACMInterface acm = new ACMInterface("http://blah.cad");
		acm.setRootNode(root.build());

		acm.exportRDFToFile("cad-model.rdf");
		acm.exportSemanticDataToFile("cad-model.bin");
	}
	
	public static void main(String[] args) {
		IUICadData inter = new IUICadData();
		inter.run();		
	}
}
