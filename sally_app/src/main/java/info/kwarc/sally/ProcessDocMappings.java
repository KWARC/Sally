package info.kwarc.sally;

import java.util.HashMap;

import com.google.inject.Singleton;

@Singleton
public class ProcessDocMappings {

	HashMap<Long, HashMap<String, Long>> docMap;
	
	public ProcessDocMappings() {
		docMap = new HashMap<Long, HashMap<String,Long>>();
	}
	
	public void addMap(Long parentProcessID, String fileName, Long docProcessID) {
		HashMap<String, Long> ref = docMap.get(parentProcessID);
		if (ref == null) {
			ref = new HashMap<String, Long>();
			docMap.put(parentProcessID, ref);
		}
		
		ref.put(fileName, docProcessID);
	}
	
	public Long getMap(Long parentProcessID, String fileName) {
		HashMap<String, Long> ref = docMap.get(parentProcessID);
		if (ref == null) {
			return null;
		}
		
		return ref.get(fileName);
	}
}
