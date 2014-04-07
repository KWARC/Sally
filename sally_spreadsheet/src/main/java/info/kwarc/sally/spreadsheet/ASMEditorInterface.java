package info.kwarc.sally.spreadsheet;

import freemarker.template.TemplateException;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.ProcessInstance;
import info.kwarc.sally.core.workflow.WorkflowUtils;
import info.kwarc.sally.networking.TemplateEngine;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import javax.ws.rs.FormParam;
import javax.ws.rs.GET;
import javax.ws.rs.POST;
import javax.ws.rs.Path;
import javax.ws.rs.QueryParam;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import Sally.AlexRangeRequest;
import Sally.RangeSelection;

import com.google.inject.Inject;

@Path("/sally/asmeditor")
public class ASMEditorInterface {

	String name;
	String ontology;
	Logger log;
	ISallyWorkflowManager kb;
	TemplateEngine templ;
	DocumentManager docManager;

	@Inject
	public ASMEditorInterface(ISallyWorkflowManager kb, TemplateEngine templ, DocumentManager docManager) {
		log = LoggerFactory.getLogger(ASMEditorInterface.class);
		this.kb = kb;
		this.docManager = docManager;
		this.templ = templ;
	}

	@GET
	public String generateUI(@QueryParam("pid") Long processInstanceID) throws IOException, TemplateException {
		ProcessInstance  pi = kb.getProcessInstance(processInstanceID);
		if (pi == null) {
			return "invalid session";
		}

		Map<String, Object> vars = pi.getProcessVariables();
		if (vars == null ){
			return "invalid session";
		}

		RangeSelection cellPosition = WorkflowUtils.getFirstTypedParameter(vars, RangeSelection.class);
		if (cellPosition == null) {
			return "session did not provide a valid cell range";
		}

		Map<String, Object> templateData = new HashMap<String, Object>();
		templateData.put("WorksheetName", "pipe-end.xls");
		templateData.put("SheetNames", new String[]{"sheet1", "sheet2"});

		templateData.put("Sheet", cellPosition.getSheet());
		templateData.put("StartRow", Integer.toString(cellPosition.getStartRow()));
		templateData.put("StartCol", Integer.toString(cellPosition.getStartCol()));
		templateData.put("EndRow", Integer.toString(cellPosition.getEndRow()));
		templateData.put("EndCol", Integer.toString(cellPosition.getEndCol()));
		templateData.put("token", Long.toString(processInstanceID));

		return templ.generateTemplate("asmeditor/asmeditor.ftl", templateData);
	}

	@POST
	public String respond(@QueryParam("pid") Long processInstanceID, @FormParam("rangeType") String rangeType, @FormParam("IM") String ontology){
		ProcessInstance  pi = kb.getProcessInstance(processInstanceID);
		if (pi == null) {
			return "invalid session";
		}

		Map<String, Object> vars = pi.getProcessVariables();
		if (vars == null ){
			return "session has no variables";
		}

		RangeSelection cellPosition = WorkflowUtils.getFirstTypedParameter(vars, RangeSelection.class);
		if (cellPosition == null) {
			return "session did not provide a valid cell range";
		}

		SpreadsheetDocument doc = WorkflowUtils.getFirstTypedParameter(vars, SpreadsheetDocument.class);
		if (doc == null) {
			return "not document found";
		}

		INetworkSender sender = docManager.getDocumentInformation(pi.getId()).getNetworkSender();
		AlexRangeRequest rangeRequest = AlexRangeRequest.newBuilder().setFileName(doc.getFilePath()).addSelection(cellPosition).build();
		sender.sendMessage("/service/get/data", rangeRequest);

		return "ok";
	}
}
