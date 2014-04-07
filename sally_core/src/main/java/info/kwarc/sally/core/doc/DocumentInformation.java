package info.kwarc.sally.core.doc;

import info.kwarc.sally.core.composition.SallyInteraction;
import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sally.core.theo.Theo;

/**
 * 
 * @author Constantin Jucovschi
 *
 * DocumentInformation class stores metadata information of a document administered by Sally. 
 * It contains information like:
 * 	  - file name
 *   - ID of the root workflow administering interaction events
 *   - Theo instance that interacts with the user
 *   - NetworkSender that allows communication with the Alex associated with this document
 *   - DocumentModel of the document
 */
public class DocumentInformation {

	String fileName;
	Long documentWorkflowID;
	Theo theo;
	INetworkSender networkSender;
	Object documentModel;
	SallyInteraction interaction;
	
	public DocumentInformation(String fileName, Long documentWorkflowID) {
		this.fileName = fileName;
		this.documentWorkflowID = documentWorkflowID;
		interaction = new SallyInteraction();
	}
	
	public SallyInteraction getInteraction() {
		return interaction;
	}
	
	public Object getDocumentModel() {
		return documentModel;
	}
	
	public void setDocumentModel(Object documentModel) {
		this.documentModel = documentModel;
	}
	
	public String getFileName() {
		return fileName;
	}
	
	public INetworkSender getNetworkSender() {
		return networkSender;
	}
	
	public void setNetworkSender(INetworkSender networkSender) {
		this.networkSender = networkSender;
	}

	public Long getDocumentWorkflowID() {
		return documentWorkflowID;
	}

	public Theo getTheo() {
		return theo;
	}

	public void setTheo(Theo theo) {
		this.theo = theo;
	}
	
	
}
