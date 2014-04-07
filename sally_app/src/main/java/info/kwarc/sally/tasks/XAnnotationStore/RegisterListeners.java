package info.kwarc.sally.tasks.XAnnotationStore;

import info.kwarc.sally.core.composition.SallyContext;
import info.kwarc.sally.core.composition.SallyInteraction;
import info.kwarc.sally.core.composition.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.composition.SallyService;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;
import XAnnotationStore.GetAnnotationsFromSelectionRequest;
import XSelectionProvider.OnSelect;

import com.google.inject.Inject;

@SallyTask(action="XAnnotationStore.RegisterListeners")
public class RegisterListeners implements WorkItemHandler {

	DocumentManager docMap;

	@Inject
	public RegisterListeners(DocumentManager docMap) {
		this.docMap = docMap;
	}

	@SallyService
	public void onSelectionRightClick(OnSelect selection, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		try {
			Long callbackID = context.getContextVar("CallbackID", Long.class);
			INetworkSender sender = docMap.getDocumentInformation(context.getContextVar("processInstanceId", Long.class)).getNetworkSender();
			GetAnnotationsFromSelectionRequest req = GetAnnotationsFromSelectionRequest.newBuilder().setCallbackid(callbackID).setFileName(selection.getFileName()).setSelectData(selection.getObjData()).build();
			sender.sendMessage("/test", req);
		} catch (Exception e) {
		}
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		try {
			SallyInteraction interaction = docMap.getDocumentInformation(workItem).getInteraction();
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
