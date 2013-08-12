package info.kwarc.sally.spreadsheet;

import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import java.util.HashMap;
import java.util.Map;

import javax.ws.rs.GET;

import org.drools.runtime.process.ProcessInstance;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.AlexClick;
import sally.RangeSelection;

import com.google.inject.Inject;

public class ASMEditor {

	Logger log;
	ISallyKnowledgeBase kb;

	@Inject
	public ASMEditor(ISallyKnowledgeBase kb) {
		log = LoggerFactory.getLogger(getClass());
		this.kb = kb;
	}

	@SallyService
	public void ASMEditService(AlexClick cell, SallyInteractionResultAcceptor acceptor, final SallyContext context) {
		final Long processInstanceID = context.getContextVar("processInstanceId", Long.class);

		ProcessInstance pi = kb.getProcessInstance(processInstanceID);
		Map<String, Object> vars = HandlerUtils.getProcessVariables(pi);

		final WorksheetDocument doc = HandlerUtils.getFirstTypedParameter(vars, WorksheetDocument.class);
		if (doc == null) {
			log.warn("No variables attached to process "+processInstanceID);
			return;
		}

		/*
		acceptor.acceptResult(new SallyMenuItem("Knowledge Base", "Show ontology link manager") {
			@Override
			public void run() {
				TheoOpenWindow window = TheoOpenWindow.newBuilder()
						.setPosition(ScreenCoordinates.newBuilder().setX(100).setY(100).build())
						.setSizeX(400).setSizeY(500).setTitle("Create Link to Ontology")
						.setUrl("http://localhost:8080/asmeditor?s="+processInstanceID).build();
				Integer wndid = sally.getOneInteraction(window, Integer.class);
				context.setContextVar("ACMEditorWindowID", wndid);
			}
		});
		 */

		final RangeSelection selection = cell.getRange();
		if (doc.getFBForRange(selection).size()==0 || doc.getLabelsForRange(selection).size()==0) {
			acceptor.acceptResult(new SallyMenuItem("Knowledge Base", "Create ontology links") {
				@Override
				public void run() {
					HashMap<String, Object>  input = new  HashMap<String, Object>();
					input.put("SelectionInput", selection);
					input.put("AbstractSpreadsheetInput", doc);
					kb.startProcess(processInstanceID, "Sally.asm_createlink", input);
				}
			});
		}
	}

	@GET
	public String editor() {
		return "hi";
	}

}
