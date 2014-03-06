package info.kwarc.sally.spreadsheet;

import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.composition.SallyContext;
import info.kwarc.sally.core.composition.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.composition.SallyService;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.ProcessInstance;
import info.kwarc.sally.core.workflow.WorkflowUtils;

import java.util.HashMap;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.AlexClick;

import com.google.inject.Inject;

public class ASMEditor {

	Logger log;
	ISallyWorkflowManager kb;

	@Inject
	public ASMEditor(ISallyWorkflowManager kb) {
		log = LoggerFactory.getLogger(getClass());
		this.kb = kb;
	}

	@SallyService
	public void ASMEditService(final AlexClick click, SallyInteractionResultAcceptor acceptor, final SallyContext context) {
		final Long processInstanceID = context.getContextVar("processInstanceId", Long.class);

		ProcessInstance pi = kb.getProcessInstance(processInstanceID);
		Map<String, Object> vars = pi.getProcessVariables();

		final SpreadsheetDocument doc = WorkflowUtils.getFirstTypedParameter(vars, SpreadsheetDocument.class);
		if (doc == null) {
			log.warn("No variables attached to process "+processInstanceID);
			return;
		}

		acceptor.acceptResult(new SallyMenuItem("Knowledge Base", "Show ontology link manager", "Create ontology link") {
			@Override
			public void run() {
				Map<String, Object> param = new HashMap<String, Object>();
				param.put("SelectedRangeInput", click.getRange());
				kb.startProcess(processInstanceID, "Sally.asm_createlink", param);
			}
		});
	}
}
