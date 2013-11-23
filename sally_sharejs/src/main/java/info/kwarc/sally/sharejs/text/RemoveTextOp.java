package info.kwarc.sally.sharejs.text;

import java.io.IOException;

import com.fasterxml.jackson.core.JsonGenerator;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.JsonSerializable;
import com.fasterxml.jackson.databind.SerializerProvider;
import com.fasterxml.jackson.databind.jsontype.TypeSerializer;

public class RemoveTextOp implements IBasicTextOp, JsonSerializable {
	int len;

	public RemoveTextOp(int len) {
		this.len = len;
	}

	public int getLen() {
		return len;
	}

	public void setLen(int len) {
		this.len = len;
	}
	
	void doWrite(JsonGenerator arg0) throws IOException, JsonProcessingException {
		if (len > 0) {
			arg0.writeStartObject();
			arg0.writeFieldName("d");
			arg0.writeNumber(len);
			arg0.writeEndObject();
		}
	}

	@Override
	public void serialize(JsonGenerator arg0, SerializerProvider arg1)
			throws IOException, JsonProcessingException {
		doWrite(arg0);
	}

	@Override
	public void serializeWithType(JsonGenerator arg0, SerializerProvider arg1,
			TypeSerializer arg2) throws IOException, JsonProcessingException {
		doWrite(arg0);
	}
}
