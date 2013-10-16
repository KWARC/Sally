package info.kwarc.sally.spreadsheet;

import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import java.util.HashMap;
import java.util.Map;

import org.drools.runtime.process.ProcessInstance;
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
		Map<String, Object> vars = HandlerUtils.getProcessVariables(pi);

		final SpreadsheetDocument doc = HandlerUtils.getFirstTypedParameter(vars, SpreadsheetDocument.class);
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
