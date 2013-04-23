

import info.kwarc.sissi.model.document.cad.ACMInterface;
import info.kwarc.sissi.model.document.cad.ACMNode;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;

import com.hp.hpl.jena.rdf.model.Model;

public class IUICadData {

	public IUICadData() {
	}

	public Model run() {
		ACMNode root = ACMNode.createNode("pipe_end");
		String ht = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexthread.omdoc?ISOhexthread?ISOhexthread";
		String ct = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/components.omdoc?component?component";
		root.addChild(ACMNode.createNode("bolt1").addProperty(ht, "M15").addProperty(ct, "bolt"));
		root.addChild(ACMNode.createNode("bolt2").addProperty(ht, "M15").addProperty(ct, "bolt"));
		root.addChild(ACMNode.createNode("bolt3").addProperty(ht, "M15").addProperty(ct, "bolt"));
		root.addChild(ACMNode.createNode("bolt4").addProperty(ht, "M15").addProperty(ct, "bolt"));
		
		ACMInterface acm = new ACMInterface();
		return acm.serialize("http://blah.cad", root);
	}
	
	public static void main(String[] args) {
		IUICadData inter = new IUICadData();
		Model model = inter.run();
		
		OutputStream file;
		try {
			file = new FileOutputStream("cad-model.rdf");
			model.write(file);
			file.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
