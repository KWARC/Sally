package info.kwarc.sally.tasks;

import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.composition.SallyContext;
import info.kwarc.sally.core.composition.SallyInteraction;
import info.kwarc.sally.core.composition.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.composition.SallyService;
import info.kwarc.sally.core.doc.DocumentInformation;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;
import sally_comm.ProtoUtils;
import XSelectionProvider.OnSelect;

import com.google.inject.Inject;
import com.google.protobuf.AbstractMessage;

@SallyTask(action="XSelectionProvider.RegisterListeners")
public class RegisterListeners implements WorkItemHandler {

	DocumentManager docMap;

	@Inject
	public RegisterListeners(DocumentManager docMap) {
		this.docMap = docMap;
	}

	@SallyService
	public void onSelectionRightClick(OnSelect selection, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		try {
			AbstractMessage msg = ProtoUtils.deserialize(selection.getObjData());
			acceptor.acceptResult(context.getCurrentInteraction().getPossibleInteractions(msg, SallyMenuItem.class));			
		} catch (Exception e) {	
		}
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		try {
			DocumentInformation di = docMap.getDocumentInformation(workItem);
			SallyInteraction interaction = di.getInteraction();
			interaction.registerServices(this);
		} catch (Exception e) {

		} finally {
			manager.completeWorkItem(workItem);
		}
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {

	}


}
