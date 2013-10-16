package info.kwarc.sally.core;

import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sally.core.theo.Theo;

public class DocumentInformation {

	String fileName;
	Long documentWorkflowID;
	Theo theo;
	INetworkSender networkSender;
	Object documentModel;
	
	public DocumentInformation(String fileName, Long documentWorkflowID) {
		this.fileName = fileName;
		this.documentWorkflowID = documentWorkflowID;
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
